package de.tudresden.inf.lat.tboxexploration

import java.lang.reflect.Field
import java.util.Collections

import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.frame.AxiomListFrame
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.semanticweb.owlapi.model.OWLAxiom

import com.google.common.collect.Sets

import Util._
import com.google.common.collect.Lists
import conexp.fx.core.collections.setlist.HashSetArrayList
import java.util.Comparator
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import org.protege.editor.owl.ui.frame.AbstractOWLFrame
import org.protege.editor.owl.ui.frame.AxiomListFrameSection

private class OrderedOWLAxiomListFrame(owlEditorKit: OWLEditorKit)
  extends AbstractOWLFrame[java.util.Set[OWLAxiom]](owlEditorKit.getModelManager().getOWLOntologyManager()) {
  addSection(new AxiomListFrameSection(owlEditorKit, this) {
    private var rowComparator: Comparator[OWLFrameSectionRow[java.util.Set[OWLAxiom], OWLAxiom, OWLAxiom]] = _
    override def getRowComparator(): Comparator[OWLFrameSectionRow[java.util.Set[OWLAxiom], OWLAxiom, OWLAxiom]] = { this.rowComparator }
    //        def setRowComparator(c: Comparator[OWLFrameSectionRow[java.util.Set[OWLAxiom], OWLAxiom, OWLAxiom]]) {
    //          this.rowComparator = c
    //        }
  });
}

class OWLAxiomList(title: String, owlEditorKit: OWLEditorKit)
  //  extends OWLFrameList[java.util.Set[OWLAxiom]](owlEditorKit, new AxiomListFrame(owlEditorKit)) {
  extends OWLFrameList[java.util.Set[OWLAxiom]](owlEditorKit, new OrderedOWLAxiomListFrame(owlEditorKit)) {

  setPrivateFields()

  private def setPrivateFields() {
    val frameField = findDeclaredField(this.getClass(), "frame")
    frameField.setAccessible(true)
    val frame = frameField.get(this).asInstanceOf[OrderedOWLAxiomListFrame]
    val frameSection = frame.getFrameSections().get(0)
    val labelField = findDeclaredField(frameSection.getClass(), "label")
    labelField.setAccessible(true)
    labelField.set(frameSection, title)
    val rowComparatorField = findDeclaredField(frameSection.getClass(), "rowComparator")
    rowComparatorField.setAccessible(true)
    rowComparatorField.set(frameSection, new Comparator[OWLFrameSectionRow[Set[OWLAxiom], OWLAxiom, OWLAxiom]] {
      override def compare(
        o1: OWLFrameSectionRow[Set[OWLAxiom], OWLAxiom, OWLAxiom],
        o2: OWLFrameSectionRow[Set[OWLAxiom], OWLAxiom, OWLAxiom]): Int = {
        (axioms indexOf o1.getAxiom) - (axioms indexOf o2.getAxiom)
      }
    })
  }

  override protected def getButtons(value: Object): java.util.List[MListButton] = Collections.emptyList()

  private val axioms = new HashSetArrayList[OWLAxiom] // Sets.newConcurrentHashSet[OWLAxiom]

  setRootObject(axioms)

  def refresh() {
    setRootObject(axioms)
    refreshComponent()
    validate()
    repaint()
  }

  def add(axiom: OWLAxiom) {
    axioms.synchronized {
      axioms add axiom
    }
    refresh()
  }

  def remove(axiom: OWLAxiom) {
    axioms.synchronized {
      axioms remove axiom
    }
    refresh()
  }

  def clear() {
    axioms.synchronized {
      axioms.clear()
    }
    refresh()
  }

  def set(content: java.util.Set[OWLAxiom]) {
    axioms.synchronized {
      axioms.clear()
      axioms addAll content
    }
    refresh()
  }

  def forEach(consumer: OWLAxiom ⇒ Unit) {
    axioms.synchronized {
      axioms.forEach(consumer(_))
    }
  }

  override def dispose() {
    axioms.synchronized {
      axioms.clear()
    }
    super.dispose()
  }

}