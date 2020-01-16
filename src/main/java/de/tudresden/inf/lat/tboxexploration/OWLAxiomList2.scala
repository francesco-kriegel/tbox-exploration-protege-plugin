package de.tudresden.inf.lat.tboxexploration

import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.frame.AbstractOWLFrame
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.semanticweb.owlapi.model.OWLAxiom
import org.protege.editor.owl.ui.frame.AxiomListFrameSection
import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import java.util.concurrent.ConcurrentHashMap
import java.util.Collections
import scala.collection.JavaConverters._
import com.google.common.collect.Sets
import org.protege.editor.owl.ui.frame.AbstractOWLFrameSection

class OWLAxiomList2(
  private val owlEditorKit: OWLEditorKit)
  extends OWLFrameList[java.util.Set[OWLAxiom]](
    owlEditorKit,
    new AbstractOWLFrame[java.util.Set[OWLAxiom]](owlEditorKit.getOWLModelManager().getOWLOntologyManager()) {

      override def setRootObject(rootObject: java.util.Set[OWLAxiom]) {}

      override def refill() {
        getFrameSections().forEach(frameSection ⇒ {
          frameSection
            .asInstanceOf[AbstractOWLFrameSection[java.util.Set[OWLAxiom], OWLAxiom, OWLAxiom]]
            .setRootObject(Collections.emptySet[OWLAxiom]())
        })
      }

    }) {

  private val frame = {
    val frameField = Util.findDeclaredField(this.getClass(), "frame")
    frameField.setAccessible(true)
    frameField.get(this).asInstanceOf[AbstractOWLFrame[java.util.Set[OWLAxiom]]]
  }

  private val _getButtons = new ConcurrentHashMap[AxiomListFrameSection, OWLAxiom ⇒ java.util.List[MListButton]]
  private val sections = new ConcurrentHashMap[String, AxiomListFrameSection]

  def addSection(id: String, title: String, getButtons: OWLAxiom ⇒ java.util.List[MListButton]) {
    val section = new AxiomListFrameSection(owlEditorKit, frame) {
      private var rootObject: java.util.Set[OWLAxiom] = _
      override def getRootObject(): java.util.Set[OWLAxiom] = { rootObject }
      override def setRootObject(rootObject: java.util.Set[OWLAxiom]) {
        this.rootObject = rootObject
        super.setRootObject(rootObject)
      }
    }
    section.setRootObject(Sets.newConcurrentHashSet[OWLAxiom])
    val labelField = Util.findDeclaredField(section.getClass(), "label")
    labelField.setAccessible(true)
    labelField.set(section, title)
    _getButtons.put(section, getButtons)
    sections.put(id, section)
    frame.getFrameSections().add(section)
  }

  override protected def getButtons(value: Object): java.util.List[MListButton] = {
    if (value.isInstanceOf[OWLFrameSectionRow[_, _, _]]) {
      val buttons = new java.util.ArrayList[MListButton]
      val frameRow: OWLFrameSectionRow[_, OWLAxiom, _] = value.asInstanceOf[OWLFrameSectionRow[_, OWLAxiom, _]];
      _getButtons.get(frameRow.getFrameSection())(frameRow.getAxiom())
    } else
      Collections.emptyList()
  }

  def refresh() {
    setRootObject(null)
    refreshComponent()
    repaint()
    validate()
  }

  def add(id: String, axiom: OWLAxiom) {
    (sections get id).getRootObject() add axiom
    refresh()
  }

  def remove(id: String, axiom: OWLAxiom) {
    (sections get id).getRootObject() remove axiom
    refresh()
  }

  def clear(id: String) {
    (sections get id).getRootObject().clear()
    refresh()
  }

  def forEach(id: String, consumer: OWLAxiom ⇒ Unit) {
    (sections get id).getRootObject().forEach(consumer(_))
  }

  override def dispose() {
    _getButtons.clear()
    sections.clear()
    super.dispose()
  }

}