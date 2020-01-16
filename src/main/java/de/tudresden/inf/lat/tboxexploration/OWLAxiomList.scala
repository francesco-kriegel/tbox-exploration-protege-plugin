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

class OWLAxiomList(title: String, owlEditorKit: OWLEditorKit)
  extends OWLFrameList[java.util.Set[OWLAxiom]](owlEditorKit, new AxiomListFrame(owlEditorKit)) {

  setTitle()

  private def setTitle() {
    val frameField = findDeclaredField(this.getClass(), "frame")
    frameField.setAccessible(true)
    val frame = frameField.get(this).asInstanceOf[AxiomListFrame]
    val frameSection = frame.getFrameSections().get(0)
    val labelField = findDeclaredField(frameSection.getClass(), "label")
    labelField.setAccessible(true)
    labelField.set(frameSection, title)
  }

  override protected def getButtons(value: Object): java.util.List[MListButton] = Collections.emptyList()

  private val axioms = Sets.newConcurrentHashSet[OWLAxiom]

  setRootObject(axioms)

  def refresh() {
    setRootObject(axioms)
    refreshComponent()
    validate()
    repaint()
  }

  def add(axiom: OWLAxiom) {
    axioms add axiom
    refresh()
  }

  def remove(axiom: OWLAxiom) {
    axioms remove axiom
    refresh()
  }

  def clear() {
    axioms.clear()
    refresh()
  }

  def set(content: java.util.Set[OWLAxiom]) {
    axioms.clear()
    axioms addAll content
    refresh()
  }

  def forEach(consumer: OWLAxiom ⇒ Unit) {
    axioms.forEach(consumer(_))
  }

  override def dispose() {
    axioms.clear()
    super.dispose()
  }

}