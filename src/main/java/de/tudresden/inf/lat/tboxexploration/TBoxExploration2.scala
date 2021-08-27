/*-
 * #%L
 * TBox Exploration Protégé Plugin
 * %%
 * Copyright (C) 2019 - 2021 Francesco Kriegel
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package de.tudresden.inf.lat.tboxexploration

import java.util.concurrent.{ConcurrentHashMap, CountDownLatch, Future}
import java.util.concurrent.atomic.AtomicInteger
import java.util.stream.Collectors
import scala.collection.JavaConverters._
import org.protege.editor.owl.model.OWLModelManager
import org.semanticweb.owl.explanation.impl.blackbox.checker.BlackBoxExplanationGeneratorFactory
import org.semanticweb.owl.explanation.impl.blackbox.checker.DefaultBlackBoxConfiguration
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClass
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLNamedIndividual
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom
import org.semanticweb.owlapi.model.parameters.Imports
import com.google.common.collect.Lists
import com.google.common.collect.Sets
import conexp.fx.core.collections.Collections3
import conexp.fx.core.math.CachedFunction
import conexp.fx.core.math.DualClosureOperator

import javax.swing.SwingUtilities
import sun.swing.SwingUtilities2
import com.sun.java.swing.SwingUtilities3

import java.util.Collections
import de.tudresden.inf.lat.ellibrary.ELConceptDescription
import de.tudresden.inf.lat.ellibrary.ELConceptInclusion
import de.tudresden.inf.lat.ellibrary.ELInterpretation2
import de.tudresden.inf.lat.ellibrary.Signature
import de.tudresden.inf.lat.ellibrary.EL._
import de.tudresden.inf.lat.protegeextensions.Util._

abstract class TBoxExploration2(
  val roleDepth:                                Integer,
  val conjunctionSize:                          Integer,
  private val maxRank:                          Integer,
  private val exploreRoleIncompatibilityAxioms: Boolean,
  private val ontology:                         OWLOntology,
  private val unwantedConsequence:              OWLAxiom,
  private val owlModelManager:                  OWLModelManager) {

  def handleStaticAxioms(axioms: java.util.Set[OWLAxiom])
  def handleRefutableAxioms(axioms: java.util.Set[OWLAxiom])
  def handleQuestion(axiom: OWLAxiom, counter: Integer): Future[Answer]
  def handleNewCounterexample(axiom: OWLClassAssertionAxiom)
  def handleAcceptedAxiom(axiom: OWLAxiom)
  def setStatus(string: String)
  def setProgress(percentage: Integer)
  def isCancelled(): Boolean

  private val counterexamples = new ConcurrentHashMap[ELConceptDescription, OWLNamedIndividual]
  private var counterexampleInterpretation = new ELInterpretation2[ELConceptDescription]
  private val nextCounterexampleNumber = new AtomicInteger(0)
  private var staticCIs = Collections.emptySet[ELConceptInclusion]
  private val repairedCIs = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val ignoredCIs = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val confirmedRoleIncompatibilityAxioms = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val checkedBinaryRoleCompositions = Sets.newConcurrentHashSet[(IRI, IRI)]

  def start() {
    repairedCIs.clear()
    ignoredCIs.clear()
    confirmedRoleIncompatibilityAxioms.clear()
    checkedBinaryRoleCompositions.clear()
    counterexamples.clear()
    counterexampleInterpretation = new ELInterpretation2[ELConceptDescription]

    val activeOntologyIRI = if (ontology.getOntologyID().getOntologyIRI().get() == null) "" else ontology.getOntologyID().getOntologyIRI().get().toString()

    val signature = new Signature(IRI.create(""))
    var j = -1
    val namedIndividuals = Sets.newConcurrentHashSet[OWLNamedIndividual]
    ontology.getSignature().forEach({
      case owlClass: OWLClass ⇒ {
        if (!owlClass.isBuiltIn()) {
          counterexampleInterpretation.synchronized {
            counterexampleInterpretation.getConceptNameExtensionMatrix().colHeads().add(owlClass.getIRI())
          }
        }
      }
      case owlObjectProperty: OWLObjectProperty ⇒ {}
      case owlNamedIndividual: OWLNamedIndividual ⇒ {
        namedIndividuals add owlNamedIndividual
        val name = owlNamedIndividual.getIRI().toString().replaceFirst(activeOntologyIRI + "#counterexample-", "")
        try {
          val i = Integer.valueOf(name)
          j = Math.max(j, i)
        } catch { case _: NumberFormatException ⇒ {} }
      }
      case default ⇒ {}
    })
    nextCounterexampleNumber.set(j + 1)

    val canonicalModelOfABox = getCanonicalModelOfABox(ontology, owlModelManager.getOWLDataFactory())
    for (namedIndividual ← namedIndividuals.asScala) {
      val c = canonicalModelOfABox.getMostSpecificConceptDescription(namedIndividual, roleDepth)
      newCounterexample(c, namedIndividual)
    }

    val allTBoxAxioms = ontology.getTBoxAxioms(Imports.EXCLUDED)
    val (allCIs, _) = transformTBox(allTBoxAxioms)

    println("determining static and refutable part...")
    val refutablePart = Sets.newConcurrentHashSet[OWLAxiom]
    val staticPart = Sets.newConcurrentHashSet[OWLAxiom]
    if (unwantedConsequence == null) {
      refutablePart addAll allTBoxAxioms
    } else {
      val explanationGeneratorFactory =
        new BlackBoxExplanationGeneratorFactory(
          new DefaultBlackBoxConfiguration(
            owlModelManager.getOWLReasonerManager().getCurrentReasonerFactory().getReasonerFactory()))
      val explanationGenerator = explanationGeneratorFactory.createExplanationGenerator(allTBoxAxioms)
      explanationGenerator.getExplanations(unwantedConsequence).forEach(
        explanation ⇒ { refutablePart addAll explanation.getAxioms() })
      staticPart addAll allTBoxAxioms
      staticPart removeAll refutablePart
    }
    handleStaticAxioms(staticPart)
    handleRefutableAxioms(refutablePart)
    val (refutableCIs, refutableRRs) = transformTBox(refutablePart)
    val (_staticCIs, staticRRs) = transformTBox(staticPart)
    staticCIs = _staticCIs
    println("unwanted consequence: " + unwantedConsequence)
    println("static part: " + staticCIs)
    println("refutable part: " + refutableCIs)
    refutablePart.forEach(
      refutableCI ⇒ {
        refutableCI.getSignature().forEach({
          case owlClass: OWLClass ⇒ {
            if (!owlClass.isBuiltIn()) {
              signature.addConceptNames(owlClass.getIRI())
            }
          }
          case owlObjectProperty: OWLObjectProperty ⇒ {
            if (!owlObjectProperty.isBuiltIn()) {
              signature.addRoleNames(owlObjectProperty.getIRI())
            }
          }
          case owlNamedIndividual: OWLNamedIndividual ⇒ {}
          case default                                ⇒ {}
        })
      })
    println("signature of refutable part: " + signature)

    val clop_repairedCIs_staticCIs =
      restrict(
        DualClosureOperator.supremum(
          clopFromTBox(repairedCIs, roleDepth),
          clopFromTBox(staticCIs, roleDepth)),
        signature)
    val clop_refutableCIs_staticCIs_counterexamples =
      restrict(
        DualClosureOperator.infimum(
          compose(
            clopFromTBox(allCIs, roleDepth),
            clopFromTBox(confirmedRoleIncompatibilityAxioms, roleDepth)),
          (concept: ELConceptDescription) ⇒ {
            if (concept.isBot())
              concept.clone().reduce()
            else
              counterexampleInterpretation.synchronized {
                counterexampleInterpretation.getMostSpecificConceptDescription(
                  Sets.intersection(
                    counterexampleInterpretation.getExtension(concept),
                    counterexamples.keySet()),
                  roleDepth)
              }
          }),
        signature)

    abstract class AbstractPosetQueueElement[T]() {
      val upperCovers = Sets.newConcurrentHashSet[PosetQueueElement[T]]
    }

    case class PosetQueueElement[T](val value: T) extends AbstractPosetQueueElement[T]() {
      override def equals(obj: Any): Boolean = obj.isInstanceOf[PosetQueueElement[T]] && (obj.asInstanceOf[PosetQueueElement[T]].value equals value)
      override def hashCode(): Int = value.hashCode
      override def toString: String = value.toString
    }

    case class PosetQueueRoot[T]() extends AbstractPosetQueueElement[T]() {}

    class PosetQueue[T](val partialOrdering: PartialOrdering[T], val filter: T => Boolean) {

      val root = new PosetQueueRoot[T]
      val values = Sets.newConcurrentHashSet[T]

      def offer(value: T): Unit = {
        if (filter(value) && values.add(value)) {
          tryInsertBelow(root, new PosetQueueElement[T](value))
        }
      }

      private def tryInsertBelow(element: AbstractPosetQueueElement[T], newElement: PosetQueueElement[T]): Unit = {
        val smallerUpperCovers = element.upperCovers.parallelStream() filter { upperCover => partialOrdering.lt(upperCover.value, newElement.value) } collect { Collectors.toSet[PosetQueueElement[T]] }
        if (smallerUpperCovers.isEmpty) {
//          element.synchronized {
            if (!element.upperCovers.contains(newElement)) {
              val greaterUpperCovers = element.upperCovers.parallelStream() filter { upperCover => partialOrdering.gt(upperCover.value, newElement.value) } collect { Collectors.toSet[PosetQueueElement[T]] }
              element.upperCovers.removeAll(greaterUpperCovers)
              element.upperCovers.add(newElement)
              newElement.upperCovers.addAll(greaterUpperCovers)
            }
//          }
        } else {
          smallerUpperCovers.forEach(tryInsertBelow(_, newElement))
        }

      }

      def poll(): java.util.stream.Stream[T] = {
        val next = Sets.newHashSet(root.upperCovers)
        root.upperCovers.clear()
        next.forEach(element => root.upperCovers.addAll(element.upperCovers))
        next.parallelStream().map[T](_.value)
      }

      def isEmpty(): Boolean = {
        root.upperCovers.isEmpty
      }
    }

    val po = new PartialOrdering[ELConceptDescription] {
      override def lt(x: ELConceptDescription, y: ELConceptDescription): Boolean = x isSemanticallySmallerThan y
      override def gt(x: ELConceptDescription, y: ELConceptDescription): Boolean = y isSemanticallySmallerThan x
      override def lteq(x: ELConceptDescription, y: ELConceptDescription): Boolean = ???
      override def gteq(x: ELConceptDescription, y: ELConceptDescription): Boolean = ???
      override def tryCompare(x: ELConceptDescription, y: ELConceptDescription): Option[Int] = ???
    }
    def filter(concept: ELConceptDescription): Boolean = {
      conjunctionSize == 0 ||
        (concept.getConceptNames.size + concept.getExistentialRestrictions.size <= conjunctionSize &&
          concept.getExistentialRestrictions.values.parallelStream.allMatch(filter))
    }
    val candidatePosetQueue = new PosetQueue[ELConceptDescription](po, filter)
    candidatePosetQueue.offer(ELConceptDescription.top)

    var iteration = 0

    def processCandidate(candidate: ELConceptDescription) {
      def checkIfRepairIsCancelled() {
        if (isCancelled())
          throw new InterruptedException("Processing of candidate " + candidate + " has been interrupted.")
      }
      var message = "candidate: " + candidate + " from thread " + Thread.currentThread().toString()
      checkIfRepairIsCancelled()
      val closure_repairedCIs_staticCIs = clop_repairedCIs_staticCIs(candidate).reduce()
      checkIfRepairIsCancelled()
      message += "\r\n  with closure (repaired CIs and static CIs): " + closure_repairedCIs_staticCIs
      if (!closure_repairedCIs_staticCIs.isBot()) {
        if (candidate.isEquivalentTo(closure_repairedCIs_staticCIs)) {
          if (!(exploreRoleIncompatibilityAxioms && containsUnsatisfiableBinaryRoleComposition(candidate))) {
            checkIfRepairIsCancelled()
            var closure_refutableCIs_staticCIs_counterexamples = clop_refutableCIs_staticCIs_counterexamples(candidate).reduce()
            checkIfRepairIsCancelled()
            message += "\r\n  with closure (refutable CIs, static CIs, and counterexamples): " + closure_refutableCIs_staticCIs_counterexamples
            checkIfRepairIsCancelled()
            println(message)
            if (exploreRoleIncompatibilityAxioms && containsUnsatisfiableBinaryRoleComposition(closure_refutableCIs_staticCIs_counterexamples)) {
              if (!clop_refutableCIs_staticCIs_counterexamples(candidate).reduce().isBot()) throw new RuntimeException()
              closure_refutableCIs_staticCIs_counterexamples = ELConceptDescription.bot()
            }
            checkIfRepairIsCancelled()
            var ask = !candidate.isEquivalentTo(closure_refutableCIs_staticCIs_counterexamples)
            var ignore = false
            var unsatisfiablePremise = false
            while (ask) {
              checkIfRepairIsCancelled()
              ask = false
              // val question: OWLAxiom = candidate SubClassOf (closure_refutableCIs_staticCIs_counterexamples without candidate)
              val question: OWLAxiom = reduceConclusion(candidate SubClassOf closure_refutableCIs_staticCIs_counterexamples)
              val future = handleQuestion(question, counterexamples.size())
              val answer = future.get()
              answer match {
                case AcceptAnswer()               ⇒ {}
                case IgnoreAnswer()               ⇒ { ignore = true }
                case UnsatisfiablePremiseAnswer() ⇒ { unsatisfiablePremise = true }
                case DeclineAnswer(counterexample) ⇒ {
                  val m = nextCounterexampleNumber.getAndIncrement()
                  val n = new AtomicInteger(0)
                  newCounterexample(counterexample, owlModelManager.getOWLDataFactory().getOWLNamedIndividual(IRI.create(activeOntologyIRI + "#counterexample-" + m)))
                  getImplicitCompletelySpecifiedCounterexamples(counterexample).foreach(implicitCounterexample ⇒
                    newCounterexample(implicitCounterexample, owlModelManager.getOWLDataFactory().getOWLNamedIndividual(IRI.create(activeOntologyIRI + "#counterexample-" + m + "." + n.incrementAndGet()))))
                  // newCounterexample(counterexample, owlModelManager.getOWLDataFactory().getOWLNamedIndividual(IRI.create(activeOntologyIRI + "#counterexample-" + nextCounterexampleNumber.getAndIncrement())))
                  closure_refutableCIs_staticCIs_counterexamples = clop_refutableCIs_staticCIs_counterexamples(candidate).reduce()
                  println("  new counterexample: " + toELConceptDescription(counterexample)
                    + "\r\n  updated closure (refutable CIs, static CIs, and counterexamples): " + closure_refutableCIs_staticCIs_counterexamples)
                  ask = !candidate.isEquivalentTo(closure_refutableCIs_staticCIs_counterexamples)
                }
                case InheritedDeclineAnswer() ⇒ {
                  closure_refutableCIs_staticCIs_counterexamples = clop_refutableCIs_staticCIs_counterexamples(candidate).reduce()
                  println("  updated closure (refutable CIs, static CIs, and counterexamples): " + closure_refutableCIs_staticCIs_counterexamples)
                  ask = !candidate.isEquivalentTo(closure_refutableCIs_staticCIs_counterexamples)
                }
              }
            }
            if (unsatisfiablePremise) {
              newConceptInclusion(candidate SubClassOf Nothing, false)
            } else {
              closure_refutableCIs_staticCIs_counterexamples = clop_refutableCIs_staticCIs_counterexamples(candidate).reduce()
              if (!candidate.isEquivalentTo(closure_refutableCIs_staticCIs_counterexamples)) {
                // val ci = candidate SubClassOf (closure_refutableCIs_staticCIs_counterexamples without candidate)
                val ci = reduceConclusion(candidate SubClassOf closure_refutableCIs_staticCIs_counterexamples)
                newConceptInclusion(ci, ignore)
              }
              checkIfRepairIsCancelled()
              closure_refutableCIs_staticCIs_counterexamples.lowerNeighborsB(signature).forEach(lowerNeighbor ⇒
                if (lowerNeighbor.roleDepth() <= roleDepth) candidatePosetQueue.offer(lowerNeighbor.reduce()))
            }
          }
        } else {
          checkIfRepairIsCancelled()
          if (!closure_repairedCIs_staticCIs.isBot())
            candidatePosetQueue.offer(closure_repairedCIs_staticCIs)
          println(message)
        }
      } else {
        println(message)
      }
    }

    while (!candidatePosetQueue.isEmpty) {
      if (isCancelled())
        throw new InterruptedException("Repair process has been interrupted.")
      iteration += 1
      println("iteration: " + iteration)
      setStatus("iteration: " + iteration)
      println("repaired TBox: " + repairedCIs)
      println("counterexamples: " + counterexamples)
      candidatePosetQueue.poll() forEach { processCandidate(_) }
    }

    println("Repair finished.")
    setStatus("Repair finished.")

    println("Writing changes to ontology...")
    val _repairedTBox = Sets.newHashSet[OWLAxiom]
    repairedCIs.removeAll(ignoredCIs)
    repairedCIs.forEach(_repairedTBox add _)
    val providedCounterexamples = Sets.newHashSet[OWLAxiom]
    counterexamples.entrySet().forEach(counterexample ⇒
      providedCounterexamples.add(owlModelManager.getOWLDataFactory().getOWLClassAssertionAxiom(counterexample.getKey().toOWLClassExpression(), counterexample.getValue())))
    synchronouslyOnProtegeThread {
      println("Removing old concept inclusions...")
      owlModelManager.getOWLOntologyManager().removeAxioms(ontology, refutablePart)
      println("Now adding new concept inclusions...")
      owlModelManager.getOWLOntologyManager().addAxioms(ontology, _repairedTBox)
      println("Now adding new counterexamples...")
      owlModelManager.getOWLOntologyManager().addAxioms(ontology, providedCounterexamples)
      println("Changes successfully written to ontology.")
    }
  }

  def getImplicitCompletelySpecifiedCounterexamples(c: ELConceptDescription): Set[ELConceptDescription] = {
    def recurse(c: ELConceptDescription, d: Integer): Set[ELConceptDescription] = {
      c.getExistentialRestrictions.values.stream.reduce[Set[ELConceptDescription]](
        if (c.roleDepth < d) Set(c) else Set(),
        (set, filler) ⇒ { set ++ recurse(filler, d - 1) },
        (set1, set2) ⇒ set1 ++ set2)
    }
    c.getExistentialRestrictions.values.stream.reduce[Set[ELConceptDescription]](
      Set(),
      (set, filler) ⇒ { set ++ recurse(filler, roleDepth - 1) },
      (set1, set2) ⇒ set1 ++ set2)
  }

  def getViolatedConceptInclusionsAsOWLAxioms(conceptDescription: ELConceptDescription): java.util.Set[OWLAxiom] = {
    val violatedConceptInclusions = Sets.newConcurrentHashSet[OWLAxiom]
    val completelySpecifiedCounterexamples =
      Set(conceptDescription) ++ getImplicitCompletelySpecifiedCounterexamples(conceptDescription)
    Sets.union(staticCIs, repairedCIs).forEach(ci ⇒ {
      //      if (!(conceptDescription satisfies ci))
      if (completelySpecifiedCounterexamples exists { c ⇒ !(c satisfies ci) })
        violatedConceptInclusions.add(ci)
    })
    violatedConceptInclusions
  }

  def getViolatedConceptInclusions(conceptDescription: ELConceptDescription): java.util.Set[ELConceptInclusion] = {
    val violatedConceptInclusions = Sets.newConcurrentHashSet[ELConceptInclusion]
    val completelySpecifiedCounterexamples =
      Set(conceptDescription) ++ getImplicitCompletelySpecifiedCounterexamples(conceptDescription)
    Sets.union(staticCIs, repairedCIs).forEach(ci ⇒ {
      //      if (!(conceptDescription satisfies ci))
      if (completelySpecifiedCounterexamples exists { c ⇒ !(c satisfies ci) })
        violatedConceptInclusions.add(ci)
    })
    violatedConceptInclusions
  }

  def saturateCounterexample(counterexample: ELConceptDescription): ELConceptDescription = {
    clopFromTBox(Sets.union(staticCIs, repairedCIs), roleDepth)(counterexample)
  }

  def repairedOntologyBecomesInconsistent(axiom: OWLAxiom): Boolean = {
    axiom match {
      case owlSubClassOfAxiom: OWLSubClassOfAxiom ⇒ {
        val newRepairedTBox = new java.util.HashSet(repairedCIs)
        newRepairedTBox add owlSubClassOfAxiom
        clopFromTBox(newRepairedTBox, 0)(ELConceptDescription.top()).isBot() ||
          counterexamples.keySet().parallelStream().anyMatch(counterexample ⇒
            clopFromTBox(newRepairedTBox, counterexample.roleDepth())(counterexample).isBot())
      }
      case owlSubPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
        false
      }
    }
  }

  def isACheckedBinaryRoleComposition(binaryRoleComposition: (IRI, IRI)): Boolean = {
    checkedBinaryRoleCompositions contains binaryRoleComposition
  }

  private def containsUnsatisfiableBinaryRoleComposition(conceptDescription: ELConceptDescription): Boolean = {
    var containsUnsatisfiableBinaryRoleComposition = false
    val uncheckedBinaryRoleCompositionsInCandidate = getAllBinaryRoleCompositionsIn(conceptDescription)
    uncheckedBinaryRoleCompositionsInCandidate.removeAll(checkedBinaryRoleCompositions)
    uncheckedBinaryRoleCompositionsInCandidate.parallelStream().forEach({
      case (role1, role2) ⇒ {
        val question = owlModelManager.getOWLDataFactory().getOWLSubPropertyChainOfAxiom(
          Lists.newArrayList(
            owlModelManager.getOWLDataFactory().getOWLObjectProperty(role1),
            owlModelManager.getOWLDataFactory().getOWLObjectProperty(role2)),
          owlModelManager.getOWLDataFactory().getOWLBottomObjectProperty())
        val future = handleQuestion(question, counterexamples.size())
        val answer = future.get()
        answer match {
          case AcceptAnswer() ⇒ {
            val roleIncompatibilityAxiom = role1 some (role2 some Thing) SubClassOf Nothing
            // newConceptInclusion(roleIncompatibilityAxiom, false)
            repairedCIs add roleIncompatibilityAxiom
            handleAcceptedAxiom(question)
            confirmedRoleIncompatibilityAxioms.add(roleIncompatibilityAxiom)
            containsUnsatisfiableBinaryRoleComposition = true
          }
          case DeclineAnswerWithoutCounterexample() ⇒ {}
          case InheritedDeclineAnswer()             ⇒ {}
        }
        checkedBinaryRoleCompositions add (role1, role2)
      }
    })
    containsUnsatisfiableBinaryRoleComposition
  }

  private def newConceptInclusion(conceptInclusion: ELConceptInclusion, ignore: Boolean) {
    repairedCIs add conceptInclusion
    if (ignore)
      ignoredCIs add conceptInclusion
    else
      handleAcceptedAxiom(conceptInclusion)
  }

  private def newCounterexample(counterexample: ELConceptDescription, individual: OWLNamedIndividual) {
    insertCounterexample(counterexample)
    counterexamples.put(counterexample, individual)
    checkedBinaryRoleCompositions addAll getAllBinaryRoleCompositionsIn(counterexample)
    handleNewCounterexample(owlModelManager.getOWLDataFactory().getOWLClassAssertionAxiom(counterexample, individual))
  }

  private def insertCounterexample(c: ELConceptDescription) {
    counterexampleInterpretation.synchronized {
      counterexampleInterpretation.getConceptNameExtensionMatrix().rowHeads().add(c)
      counterexampleInterpretation.getConceptNameExtensionMatrix().colHeads().addAll(c.getConceptNames())
      counterexampleInterpretation.getConceptNameExtensionMatrix().row(c).addAll(c.getConceptNames())
      c.getExistentialRestrictions().entries().forEach(entry ⇒ {
        insertCounterexample(entry.getValue())
        val roleNameExtensionMatrix = counterexampleInterpretation.getRoleNameExtensionMatrix(entry.getKey())
        roleNameExtensionMatrix.rowHeads().add(c)
        roleNameExtensionMatrix.rowHeads().add(entry.getValue())
        roleNameExtensionMatrix.add(c, entry.getValue())
      })
    }
  }

  def dispose() {

  }

}
