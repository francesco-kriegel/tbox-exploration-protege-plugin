package de.tudresden.inf.lat.tboxexploration

import java.io.OutputStream
import java.lang.reflect.InvocationTargetException
import java.util.Collection
import java.util.Collections
import java.util.Optional
import java.util.Random
import java.util.Set
import java.util.concurrent.ExecutionException
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import java.util.function.Function

import javax.swing.SwingUtilities

import org.semanticweb.owlapi.io.OWLOntologyDocumentTarget
import org.semanticweb.owlapi.model.AxiomType
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAnnotation
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom
import org.semanticweb.owlapi.model.OWLAnnotationAxiom
import org.semanticweb.owlapi.model.OWLAnnotationProperty
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom
import org.semanticweb.owlapi.model.OWLAnnotationSubject
import org.semanticweb.owlapi.model.OWLAnonymousIndividual
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClass
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLClassAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLDataProperty
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLDataPropertyAxiom
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom
import org.semanticweb.owlapi.model.OWLDataPropertyExpression
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom
import org.semanticweb.owlapi.model.OWLDatatype
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom
import org.semanticweb.owlapi.model.OWLDeclarationAxiom
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom
import org.semanticweb.owlapi.model.OWLDocumentFormat
import org.semanticweb.owlapi.model.OWLEntity
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLHasKeyAxiom
import org.semanticweb.owlapi.model.OWLImportsDeclaration
import org.semanticweb.owlapi.model.OWLIndividual
import org.semanticweb.owlapi.model.OWLIndividualAxiom
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLLogicalAxiom
import org.semanticweb.owlapi.model.OWLNamedIndividual
import org.semanticweb.owlapi.model.OWLNamedObjectVisitor
import org.semanticweb.owlapi.model.OWLNamedObjectVisitorEx
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObject
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom
import org.semanticweb.owlapi.model.OWLObjectVisitor
import org.semanticweb.owlapi.model.OWLObjectVisitorEx
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLOntologyID
import org.semanticweb.owlapi.model.OWLOntologyManager
import org.semanticweb.owlapi.model.OWLOntologyStorageException
import org.semanticweb.owlapi.model.OWLPrimitive
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom
import org.semanticweb.owlapi.model.parameters.AxiomAnnotations
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.parameters.Navigation
import org.semanticweb.owlapi.util.OWLAxiomSearchFilter

object Util {

  private val random: Random = new Random()

  def getRandomElement[E](c: Collection[E]): Optional[E] = {
    if (c.isEmpty())
      return Optional.empty()
    return c.stream().skip(random.nextInt(c.size())).findFirst()
  }

  def randomSelector[E >: Null <: AnyRef](set: Set[E]): Future[E] =
    new Future[E]() {

      private val result: E = getRandomElement(set).orElse(null)

      override def cancel(mayInterruptIfRunning: Boolean): Boolean = false
      override def isCancelled(): Boolean = false
      override def isDone(): Boolean = true

      @throws(classOf[InterruptedException])
      @throws(classOf[ExecutionException])
      override def get(): E = result

      @throws(classOf[InterruptedException])
      @throws(classOf[ExecutionException])
      @throws(classOf[TimeoutException])
      override def get(timeout: Long, unit: TimeUnit): E = result
    }

  def runOnProtegeThread(runnable: Runnable, sync: Boolean) {
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
