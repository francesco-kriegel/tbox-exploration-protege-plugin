package de.tudresden.inf.lat.tboxexploration

import java.lang.reflect.Field
import java.lang.reflect.InvocationTargetException
import java.util.concurrent.ConcurrentHashMap

import scala.collection.JavaConverters.asScalaSetConverter

import org.semanticweb.owlapi.model.AxiomType
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.NodeID
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLDataFactory
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom
import org.semanticweb.owlapi.model.OWLIndividual
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.parameters.Imports

import com.google.common.collect.Sets

import conexp.fx.core.dl.ELConceptDescription
import conexp.fx.core.dl.ELConceptInclusion
import conexp.fx.core.dl.ELInterpretation2
import conexp.fx.core.dl.ELSyntaxException
import conexp.fx.core.dl.ELsiConceptDescription
import conexp.fx.core.math.DualClosureOperator
import javax.swing.SwingUtilities
import java.util.Collections
import conexp.fx.core.dl.Signature

object Util {

  def compatibilize(clop: DualClosureOperator[ELConceptDescription], roleDepth: Int): DualClosureOperator[ELConceptDescription] = concept ⇒ {
    val closure = concept.clone()
    //        def recursivelyClose(c: ELConceptDescription, d: Int): Boolean = {
    //          var changed = false
    //          changed |= clop.close(c)
    //          c.restrictTo(d)
    //          changed |= c.getExistentialRestrictions().values().parallelStream().map[Boolean](e ⇒ recursivelyClose(e, d - 1)).reduce(false, _ || _)
    //          changed
    //        }
    def recursivelyClose(c: ELConceptDescription, d: Int) {
      clop.close(c)
      c.restrictTo(d)
      c.getExistentialRestrictions().values().forEach(e ⇒ recursivelyClose(e, d - 1))
    }
    var changed = true
    while (changed) {
      val oldClosure = closure.clone()
      recursivelyClose(closure, roleDepth)
      changed = !(closure isEquivalentTo oldClosure)
    }
    closure
  }

  def clopFromTBox(tBox: java.util.Set[ELConceptInclusion], roleDepth: Int): DualClosureOperator[ELConceptDescription] = concept ⇒ {
    if (roleDepth < 0)
      throw new IllegalArgumentException("Role depth cannot be smaller than 0.")
    else if (concept.roleDepth() > roleDepth)
      throw new IllegalArgumentException("The role depth of the concept description exceeds the given role depth.")
    else if (concept.isBot())
      concept.clone().reduce()
    else if (tBox.isEmpty())
      concept.clone().reduce()
    else {
      val _tbox: Set[(ELsiConceptDescription[Integer], ELsiConceptDescription[Integer])] =
        Set.empty ++ tBox.asScala.map(ci ⇒
          (ELsiConceptDescription.of(ci.getSubsumee()), ELsiConceptDescription.of(ci.getSubsumer())))
      ELsiConceptDescription.of(concept).clone().mostSpecificConsequence(_tbox).approximate(roleDepth)
    }
  }

  def compose(clop1: DualClosureOperator[ELConceptDescription], clop2: DualClosureOperator[ELConceptDescription]): DualClosureOperator[ELConceptDescription] =
    concept ⇒ clop2(clop1(concept))

  def restrict(clop: DualClosureOperator[ELConceptDescription], signature: Signature): DualClosureOperator[ELConceptDescription] =
    concept ⇒ {
      if (concept.isBot())
        concept
      else if (signature.getConceptNames().containsAll(concept.getSignature().getConceptNames())
        && signature.getRoleNames().containsAll(concept.getSignature().getRoleNames()))
        clop(concept) restrictTo signature
      else
        throw new IllegalArgumentException(
          "The concept description " + concept + " contains names that are not in the given signature " + signature)
    }

  implicit def toOWLClassExpression(conceptDescription: ELConceptDescription): OWLClassExpression = {
    conceptDescription.toOWLClassExpression()
  }

  implicit def toELConceptDescription(classExpression: OWLClassExpression): ELConceptDescription = {
    new ELConceptDescription(classExpression)
  }

  implicit def toOWLSubClassOfAxiom(conceptInclusion: ELConceptInclusion): OWLSubClassOfAxiom = {
    conceptInclusion.toOWLSubClassOfAxiom()
  }

  implicit def toELConceptInclusion(subClassOfAxiom: OWLSubClassOfAxiom): ELConceptInclusion = {
    new ELConceptInclusion(subClassOfAxiom)
  }

  implicit class ImplicitBoolean(b: Boolean) {
    def ->(c: Boolean) = !b || c
  }

  implicit class ImplicitELConceptDescription[A](c: A)(implicit f: A => ELConceptDescription) {
    def and(d: ELConceptDescription) = ELConceptDescription.conjunction(c, d)
    //    def ->(d: ELConceptDescription) = new ELConceptInclusion(c, d)
    def SubClassOf(d: ELConceptDescription) = new ELConceptInclusion(c, d)
    def satisfies(ci: ELConceptInclusion) = (c isSubsumedBy ci.getSubsumee()) -> (c isSubsumedBy ci.getSubsumer())
    def restrictTo(signature: Signature): ELConceptDescription = {
      if (!c.isBot()) {
        c.getConceptNames().retainAll(signature.getConceptNames())
        c.getExistentialRestrictions().keySet().retainAll(signature.getRoleNames())
        c.getExistentialRestrictions().values() forEach { _.restrictTo(signature) }
      }
      c
    }
    def canBeSimulatedIn(d: ELConceptDescription): Boolean = {
      (c.roleDepth <= d.roleDepth) &&
        ((c subsumes d) ||
          (d.getExistentialRestrictions.values.stream anyMatch { c canBeSimulatedIn _ }))
    }
    def isSemanticallySmallerThan(d: ELConceptDescription): Boolean = {
      (c.roleDepth <= d.roleDepth) &&
        !(d subsumes c) &&
        ((c subsumes d) ||
          (d.getExistentialRestrictions.values.stream anyMatch { c canBeSimulatedIn _ }))
    }
  }

//  implicit class ImplicitOWLClassExpression(c: OWLClassExpression) {
//    def and(d: OWLClassExpression) = ELConceptDescription.conjunction(c, d)
//    def SubClassOf(d: OWLClassExpression) = new ELConceptInclusion(c, d)
//    def satisfies(ci: ELConceptInclusion) = (c isSubsumedBy ci.getSubsumee()) -> (c isSubsumedBy ci.getSubsumer())
//  }

  implicit class ImplicitRoleName(r: IRI) {
    def some(c: ELConceptDescription) = ELConceptDescription.existentialRestriction(r, c)
  }

  val Thing = ELConceptDescription.top()

  val Nothing = ELConceptDescription.bot()

  def isTautology(owlSubClassOfAxiom: OWLSubClassOfAxiom): Boolean = {
    owlSubClassOfAxiom.getSubsumee() isSubsumedBy owlSubClassOfAxiom.getSubsumer()
  }

  def isEntailed(tBox: java.util.Set[ELConceptInclusion], owlSubClassOfAxiom: OWLSubClassOfAxiom): Boolean = {
    val rd = Math.max(
      owlSubClassOfAxiom.getSubsumee().roleDepth(),
      owlSubClassOfAxiom.getSubsumer().roleDepth())
    clopFromTBox(tBox, rd)(owlSubClassOfAxiom.getSubsumee()) isSubsumedBy owlSubClassOfAxiom.getSubsumer()
  }

  def reduceConclusion(conceptInclusion: ELConceptInclusion): ELConceptInclusion = {
    val subsumee = conceptInclusion.getSubsumee().clone().reduce()
    val subsumer = conceptInclusion.getSubsumer().clone().reduce() without subsumee
    def recurse(c: ELConceptDescription) {
      Sets.newConcurrentHashSet(c.getExistentialRestrictions().values()).forEach(d ⇒ {
        if (d isSubsumedBy subsumee)
          d.set(((d without subsumer) and subsumee).reduce())
        recurse(d)
      })
    }
    recurse(subsumer)
    val result = (subsumee SubClassOf subsumer)
    if (!isEntailed(Collections.singleton(result), conceptInclusion) ||
      !isEntailed(Collections.singleton(conceptInclusion), result))
      throw new RuntimeException(
        "Method reduceConclusion() is not sound.\r\n"
          + "input: " + conceptInclusion + "\r\n"
          + "output: " + result)
    val nextSubsumer = subsumer.clone()
    recurse(nextSubsumer)
    if (!(subsumer deepEquals nextSubsumer))
      throw new RuntimeException("Method reduceConclusion() does not find minimal reductions.\r\n"
        + "input: " + conceptInclusion + "\r\n"
        + "output: " + result + "\r\n"
        + "smaller result: " + (subsumee SubClassOf nextSubsumer))
    result
  }

  def transformTBox(ontology: java.util.Set[OWLAxiom]): (java.util.Set[ELConceptInclusion], java.util.Map[IRI, ELConceptDescription]) = {
    val conceptInclusions = Sets.newConcurrentHashSet[ELConceptInclusion]
    val rangeRestrictions = new ConcurrentHashMap[IRI, ELConceptDescription]()
    ontology.forEach(axiom ⇒ {
      axiom.getAxiomType() match {
        case AxiomType.SUBCLASS_OF ⇒ {
          val subClassOfAxiom = axiom.asInstanceOf[OWLSubClassOfAxiom]
          try {
            conceptInclusions.add(new ELConceptInclusion(new ELConceptDescription(subClassOfAxiom.getSubClass()).reduce(), new ELConceptDescription(subClassOfAxiom.getSuperClass()).reduce()))
          } catch {
            case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
          }
        }
        case AxiomType.DISJOINT_CLASSES ⇒ {
          val disjointClassesAxiom = axiom.asInstanceOf[OWLDisjointClassesAxiom]
          val disjointClasses = disjointClassesAxiom.getClassExpressionsAsList()
          (0 until disjointClasses.size()).foreach(i ⇒ {
            (i + 1 until disjointClasses.size()).foreach(j ⇒ {
              try {
                conceptInclusions.add(
                  new ELConceptInclusion(
                    ELConceptDescription.conjunction(
                      new ELConceptDescription(disjointClasses.get(i)),
                      new ELConceptDescription(disjointClasses.get(j))),
                    ELConceptDescription.bot()))
              } catch {
                case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
              }
            })
          })
        }
        case AxiomType.EQUIVALENT_CLASSES ⇒ {
          val equivalentClassesAxiom = axiom.asInstanceOf[OWLEquivalentClassesAxiom]
          val equivalentClasses = equivalentClassesAxiom.getClassExpressionsAsList()
          (1 until equivalentClasses.size()).foreach(i ⇒ {
            try {
              conceptInclusions.add(
                new ELConceptInclusion(
                  new ELConceptDescription(equivalentClasses.get(i - 1)),
                  new ELConceptDescription(equivalentClasses.get(i))))
            } catch {
              case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
            }
          })
          try {
            conceptInclusions.add(
              new ELConceptInclusion(
                new ELConceptDescription(equivalentClasses.get(equivalentClasses.size() - 1)),
                new ELConceptDescription(equivalentClasses.get(0))))
          } catch {
            case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
          }
        }
        case AxiomType.OBJECT_PROPERTY_DOMAIN ⇒ {
          val domainRestrictionAxiom = axiom.asInstanceOf[OWLObjectPropertyDomainAxiom]
          val property = domainRestrictionAxiom.getProperty()
          if (property.isInstanceOf[OWLObjectProperty]) {
            val r = property.asOWLObjectProperty().getIRI()
            val dom = domainRestrictionAxiom.getDomain()
            try {
              conceptInclusions.add(
                new ELConceptInclusion(
                  ELConceptDescription.existentialRestriction(r, ELConceptDescription.top()),
                  new ELConceptDescription(dom)))
            } catch {
              case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
            }
          } else { println("cannot handle " + axiom) }
        }
        case AxiomType.OBJECT_PROPERTY_RANGE ⇒ {
          println("not yet implemented to handle " + axiom)
          val rangeRestrictionAxiom = axiom.asInstanceOf[OWLObjectPropertyRangeAxiom]
          val property = rangeRestrictionAxiom.getProperty()
          if (property.isObjectPropertyExpression()) {
            val r = property.asOWLObjectProperty().getIRI()
            val ran = rangeRestrictionAxiom.getRange()
            try {
              rangeRestrictions.put(
                r,
                ELConceptDescription.conjunction(
                  new ELConceptDescription(ran),
                  rangeRestrictions.getOrDefault(r, ELConceptDescription.top())))
            } catch {
              case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
            }
          }
        }
        case AxiomType.EQUIVALENT_OBJECT_PROPERTIES ⇒ { println("not yet implemented to handle " + axiom) }
        case AxiomType.SUB_OBJECT_PROPERTY          ⇒ { println("not yet implemented to handle " + axiom) }
        case AxiomType.SUB_PROPERTY_CHAIN_OF        ⇒ { println("not yet implemented to handle " + axiom) }
        case AxiomType.REFLEXIVE_OBJECT_PROPERTY    ⇒ { println("not yet implemented to handle " + axiom) }
        case AxiomType.TRANSITIVE_OBJECT_PROPERTY   ⇒ { println("not yet implemented to handle " + axiom) }
        case default                                ⇒ { println("cannot handle " + axiom) }
      }
    })
    (conceptInclusions, rangeRestrictions)
  }

  def getCanonicalModelOfABox(ontology: OWLOntology, owlDataFactory: OWLDataFactory): ELInterpretation2[OWLIndividual] = {
    val canonicalModelOfABox = new ELInterpretation2[OWLIndividual]
    def insertIntoCanonicalModelOfABox(individual: OWLIndividual, conceptDescription: ELConceptDescription) {
      conceptDescription.getConceptNames().forEach(conceptName ⇒ {
        canonicalModelOfABox.synchronized {
          canonicalModelOfABox add (individual, conceptName)
        }
      })
      conceptDescription.getExistentialRestrictions().entries().forEach(entry ⇒ {
        val roleName = entry.getKey()
        val fillerConceptDescription = entry.getValue()
        val targetIndividual = owlDataFactory.getOWLAnonymousIndividual(NodeID.nextAnonymousIRI())
        canonicalModelOfABox.synchronized {
          canonicalModelOfABox add (individual, roleName, targetIndividual)
        }
        insertIntoCanonicalModelOfABox(targetIndividual, fillerConceptDescription)
      })
    }
    ontology.getABoxAxioms(Imports.EXCLUDED).forEach(axiom ⇒ {
      axiom.getAxiomType() match {
        case AxiomType.CLASS_ASSERTION ⇒ {
          val classAssertionAxiom = axiom.asInstanceOf[OWLClassAssertionAxiom]
          val individual = classAssertionAxiom.getIndividual()
          val classExpression = classAssertionAxiom.getClassExpression()
          //          val individualIRI = if (individual.isNamed()) individual.asOWLNamedIndividual().getIRI() else NodeID.getIRIFromNodeID(individual.asOWLAnonymousIndividual().getID().getID())
          try {
            val conceptDescription = new ELConceptDescription(classExpression)
            insertIntoCanonicalModelOfABox(individual, conceptDescription)
          } catch {
            case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
          }
        }
        case AxiomType.OBJECT_PROPERTY_ASSERTION ⇒ {
          val objectPropertyAssertionAxiom = axiom.asInstanceOf[OWLObjectPropertyAssertionAxiom]
          val subjectIndividual = objectPropertyAssertionAxiom.getSubject()
          val objectIndividual = objectPropertyAssertionAxiom.getObject()
          val objectPropertyExpression = objectPropertyAssertionAxiom.getProperty()
          //          val subjectIndividualIRI =
          //            if (subjectIndividual.isNamed())
          //              subjectIndividual.asOWLNamedIndividual().getIRI()
          //            else NodeID.getIRIFromNodeID(subjectIndividual.asOWLAnonymousIndividual().getID().getID())
          //          val objectIndividualIRI =
          //            if (objectIndividual.isNamed())
          //              objectIndividual.asOWLNamedIndividual().getIRI()
          //            else NodeID.getIRIFromNodeID(objectIndividual.asOWLAnonymousIndividual().getID().getID())
          if (objectPropertyExpression.isInstanceOf[OWLObjectProperty]) {
            val objectPropertyIRI = objectPropertyExpression.asOWLObjectProperty().getIRI()
            canonicalModelOfABox.synchronized {
              canonicalModelOfABox add (subjectIndividual, objectPropertyIRI, objectIndividual)
            }
          } else {
            println("cannot handle " + axiom)
          }
        }
        case AxiomType.SAME_INDIVIDUAL ⇒ { println("not yet implemented to handle " + axiom) }
        case default                   ⇒ { println("cannot handle " + axiom) }
      }
    })
    canonicalModelOfABox
  }

  def addAllBinaryRoleCompositions(conceptDescription: ELConceptDescription, binaryRoleCompositions: java.util.Set[(IRI, IRI)]) {
    conceptDescription.getExistentialRestrictions().entries().forEach(entry ⇒ {
      val role1 = entry.getKey()
      val fillerConceptDescription = entry.getValue()
      fillerConceptDescription.getExistentialRestrictions().keySet().forEach(role2 ⇒ {
        binaryRoleCompositions add (role1, role2)
      })
    })
  }

  def getAllBinaryRoleCompositionsIn(conceptDescription: ELConceptDescription): java.util.Set[(IRI, IRI)] = {
    val binaryRoleCompositions = Sets.newConcurrentHashSet[(IRI, IRI)]
    addAllBinaryRoleCompositions(conceptDescription, binaryRoleCompositions)
    binaryRoleCompositions
  }

  private def runOnProtegeThread(runnable: Runnable, sync: Boolean) {
    if (SwingUtilities.isEventDispatchThread()) {
      runnable.run()
    } else {
      try {
        if (sync)
          SwingUtilities.invokeAndWait(runnable)
        else
          SwingUtilities.invokeLater(runnable)
        // System.out.println("Started on GUI thread.")
      } catch {
        case e: Error ⇒
          if (e.getMessage().equals("Cannot call invokeAndWait from the event dispatcher thread")) {
            // System.out.println("Already in GUI thread, running here.")
            runnable.run()
          } else throw new RuntimeException(e)
        case e @ (_: InvocationTargetException | _: InterruptedException) ⇒ throw new RuntimeException(e)
      }
    }
  }

  def synchronouslyOnProtegeThread(code: ⇒ Unit) {
    runOnProtegeThread(() ⇒ code, true)
  }

  def asynchronouslyOnProtegeThread(code: ⇒ Unit) {
    runOnProtegeThread(() ⇒ code, false)
  }

  def findDeclaredField(clazz: Class[_], fieldName: String): Field = {
    var currentClass = clazz
    var field: Field = null
    while (field == null && currentClass != null) {
      try {
        field = currentClass.getDeclaredField(fieldName)
      } catch {
        case _: NoSuchFieldException ⇒ {
          currentClass = currentClass.getSuperclass()
        }
      }
    }
    if (field == null)
      throw new NoSuchFieldException(fieldName)
    else
      field
  }

}
