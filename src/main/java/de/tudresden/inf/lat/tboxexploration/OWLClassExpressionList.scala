package de.tudresden.inf.lat.tboxexploration

import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.semanticweb.owlapi.model.OWLClassExpression
import org.protege.editor.owl.ui.frame.AbstractOWLFrame
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import org.protege.editor.owl.ui.frame.AbstractOWLFrameSectionRow
import org.protege.editor.owl.ui.frame.AbstractOWLFrameSection
import org.protege.editor.owl.ui.editor.OWLObjectEditor
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLAxiom
import java.util.Comparator
import org.semanticweb.owlapi.model.OWLObject

class OWLClassExpressionList(title: String, owlEditorKit: OWLEditorKit)
  extends OWLFrameList[java.util.Set[OWLClassExpression]](
    owlEditorKit,
    new AbstractOWLFrame[java.util.Set[OWLClassExpression]](owlEditorKit.getOWLModelManager.getOWLOntologyManager) {
      addSection(
        new AbstractOWLFrameSection[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression](
          owlEditorKit,
          title,
          this) {
          override protected def createAxiom(classExpression: OWLClassExpression): OWLAxiom = { null }
          override def getObjectEditor(): OWLObjectEditor[OWLClassExpression] = { null }
          override protected def refill(ontology: OWLOntology): Unit = {
            getRootObject().forEach(classExpression ⇒ {
              //              addRow(new AbstractOWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]() {
              //                TODO: the used row type can only be used with axioms but not with class expressions
              //              })
            })
          }
          override protected def clear(): Unit = {}
          override def canAdd(): Boolean = { false }

          private class RowComparator extends Comparator[OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]] {
            private val objComparator: Comparator[OWLObject] = getOWLModelManager().getOWLObjectComparator()
            override def compare(o1: OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression], o2: OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]): Int = {
              objComparator.compare(o1.getAxiom(), o2.getAxiom())
            }
          }
          private val rowComparator: RowComparator = new RowComparator()
          override def getRowComparator(): Comparator[OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]] = { rowComparator }
        })
    }) {

}