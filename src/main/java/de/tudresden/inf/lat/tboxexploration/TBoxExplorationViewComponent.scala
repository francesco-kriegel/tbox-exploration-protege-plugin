package de.tudresden.inf.lat.tboxexploration

import java.awt.BorderLayout
import java.awt.Button
import java.awt.Color
import java.awt.Dimension
import java.awt.Font
import java.awt.Graphics2D
import java.awt.GridLayout
import java.awt.Label
import java.awt.event.ActionListener
import java.util.Collections
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ExecutionException
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import java.util.concurrent.atomic.AtomicInteger
import java.util.stream.Collectors

//import scala.collection.JavaConverters._
import scala.collection.JavaConverters.asScalaSetConverter

import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.core.ui.util.InputVerificationStatusChangedListener
import org.protege.editor.owl.ui.editor.OWLClassExpressionExpressionEditor
import org.protege.editor.owl.ui.frame.AxiomListFrame
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.protege.editor.owl.ui.view.AbstractOWLViewComponent
import org.semanticweb.owlapi.model.AxiomType
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.NodeID
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClass
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom
import org.semanticweb.owlapi.model.OWLIndividual
import org.semanticweb.owlapi.model.OWLNamedIndividual
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom
import org.semanticweb.owlapi.model.parameters.Imports

import com.google.common.collect.Lists
import com.google.common.collect.Sets

import conexp.fx.core.collections.Collections3
import conexp.fx.core.dl.ELConceptDescription
import conexp.fx.core.dl.ELConceptInclusion
import conexp.fx.core.dl.ELInterpretation2
import conexp.fx.core.dl.ELSyntaxException
import conexp.fx.core.dl.ELsiConceptDescription
import conexp.fx.core.dl.Signature
import conexp.fx.core.math.DualClosureOperator
import javax.swing.JButton
import javax.swing.JLabel
import javax.swing.JOptionPane
import javax.swing.JPanel
import javax.swing.JScrollPane
import javax.swing.UIManager

class TBoxExplorationViewComponent extends AbstractOWLViewComponent {

  private var thread: Thread = _
  private val counterexamples = new ConcurrentHashMap[ELConceptDescription, OWLNamedIndividual]
  private var counterexampleInterpretation = new ELInterpretation2[ELConceptDescription]
  private val nextCounterexampleNumber = new AtomicInteger(0)
  private val repairedTBox = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val ignoredTBox = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val confirmedRoleIncompatibilityAxioms = Sets.newConcurrentHashSet[ELConceptInclusion]
  private val checkedBinaryRoleCompositions = Sets.newConcurrentHashSet[(IRI, IRI)]
  private val questions = Sets.newConcurrentHashSet[OWLAxiom]()
  private val answers = new ConcurrentHashMap[OWLAxiom, Answer]
  private val futures = new ConcurrentHashMap[(OWLAxiom, Integer), Future[Answer]]

  private var repairButton: Button = _
  private val repairButtonActionListener_Start: ActionListener = _ ⇒ startRepairThread()
  private val repairButtonActionListener_Stop: ActionListener = _ ⇒ stopRepairThread()
  private var statusLabel: Label = _
  private var counterexampleAxiomListFrame: AxiomListFrame = _
  private var counterexampleAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _
  private var confirmedAxiomListFrame: AxiomListFrame = _
  private var confirmedAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _
  private var pendingAxiomListFrame: AxiomListFrame = _
  private var pendingAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _

  private class TextMListButton(tooltipText: String, rollOverColor: Color, buttonText: String, buttonTextSize: Int, listener: ActionListener)
    extends MListButton(tooltipText: String, rollOverColor: Color, listener: ActionListener) {
    /**
     * The code of this method is copied and slightly modified from the class
     * org.exquisite.protege.ui.buttons.UnicodeButton in the Ontology Debugger Plugin for Protégé
     * @see https://git-ainf.aau.at/interactive-KB-debugging/debugger/blob/4a2e4c8ee36a8f63bf7facd099021420b0621cc9/protege-plugin/src/main/java/org/exquisite/protege/ui/buttons/UnicodeButton.java
     */
    def paintButtonContent(g: Graphics2D) {
      g.setColor(Color.WHITE)
      g.setFont(new Font(Font.SANS_SERIF, Font.BOLD, buttonTextSize));
      val stringWidth = g.getFontMetrics().getStringBounds(buttonText, g).getBounds().width;
      val w = getBounds().width;
      val h = getBounds().height;
      g.drawString(
        buttonText,
        getBounds().x + w / 2 - stringWidth / 2,
        getBounds().y + g.getFontMetrics().getAscent() / 2 + h / 2 - 2);
    }
    //              def paintBackgroundColor(g: Graphics2D, color: Color) {
    //                val buttonBounds: Rectangle = getBounds();
    //                val oldColor: Color = g.getColor();
    //                g.setColor(color);
    //                g.fillOval(buttonBounds.x, buttonBounds.y, buttonBounds.width, buttonBounds.height);
    //                g.setColor(oldColor);
    //              }
    override protected def getSizeMultiple(): Int = { 4 }
  }

  protected def initialiseOWLView() {
    println("Initializing TBox Exploration View Component...")
    //    val counterexampleFrameList = new OWLFrameList[java.util.Set[OWLClassExpression]](getOWLEditorKit(), new AbstractOWLFrame[java.util.Set[OWLClassExpression]](getOWLModelManager().getOWLOntologyManager()) {
    //      addSection(new AbstractOWLFrameSection[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression](getOWLEditorKit(), "Provided Counterexamples", this) {
    //        override protected def createAxiom(classExpression: OWLClassExpression): OWLAxiom = { null }
    //        override def getObjectEditor(): OWLObjectEditor[OWLClassExpression] = { null }
    //        override protected def refill(ontology: OWLOntology): Unit = {
    //          getRootObject().forEach(classExpression ⇒ {
    //            addRow(new AbstractOWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]() {
    //
    //            })
    //          })
    //        }
    //        override protected def clear(): Unit = {}
    //        override def canAdd(): Boolean = { false }
    //
    //        private class RowComparator extends Comparator[OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]] {
    //          private val objComparator: Comparator[OWLObject] = getOWLModelManager().getOWLObjectComparator()
    //          override def compare(o1: OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression], o2: OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]) {
    //            objComparator.compare(o1.getAxiom(), o2.getAxiom())
    //          }
    //        }
    //        private val rowComparator: RowComparator = new RowComparator()
    //        override def getRowComparator(): Comparator[OWLFrameSectionRow[java.util.Set[OWLClassExpression], OWLAxiom, OWLClassExpression]] = { rowComparator }
    //      })
    //    })

    counterexampleAxiomListFrame = new AxiomListFrame(getOWLEditorKit())
    val counterexampleFrameSection = counterexampleAxiomListFrame.getFrameSections().get(0)
    val counterexampleLabelField = counterexampleFrameSection.getClass().getSuperclass().getDeclaredField("label")
    counterexampleLabelField.setAccessible(true)
    counterexampleLabelField.set(counterexampleFrameSection, "Provided Counterexamples")
    counterexampleAxiomList =
      new OWLFrameList[java.util.Set[OWLAxiom]](getOWLEditorKit(), counterexampleAxiomListFrame) {
        override protected def getButtons(value: Object): java.util.List[MListButton] = Collections.emptyList()
      }

    confirmedAxiomListFrame = new AxiomListFrame(getOWLEditorKit())
    val confirmedFrameSection = confirmedAxiomListFrame.getFrameSections().get(0)
    val confirmedLabelField = confirmedFrameSection.getClass().getSuperclass().getDeclaredField("label")
    confirmedLabelField.setAccessible(true)
    confirmedLabelField.set(confirmedFrameSection, "Confirmed Axioms")
    confirmedAxiomList =
      new OWLFrameList[java.util.Set[OWLAxiom]](getOWLEditorKit(), confirmedAxiomListFrame) {
        override protected def getButtons(value: Object): java.util.List[MListButton] = Collections.emptyList()
      }
    pendingAxiomListFrame = new AxiomListFrame(getOWLEditorKit())
    val pendingFrameSection = pendingAxiomListFrame.getFrameSections().get(0)
    val pendingLabelField = pendingFrameSection.getClass().getSuperclass().getDeclaredField("label")
    pendingLabelField.setAccessible(true)
    pendingLabelField.set(pendingFrameSection, "Pending Axioms")

    pendingAxiomList =
      new OWLFrameList[java.util.Set[OWLAxiom]](getOWLEditorKit(), pendingAxiomListFrame) {
        override protected def getButtons(value: Object): java.util.List[MListButton] = {
          if (value.isInstanceOf[OWLFrameSectionRow[_, _, _]]) {
            val buttons = new java.util.ArrayList[MListButton]
            val frameRow: OWLFrameSectionRow[_, OWLAxiom, _] = value.asInstanceOf[OWLFrameSectionRow[_, OWLAxiom, _]];
            val axiom = frameRow.getAxiom()
            axiom match {
              case subClassOfAxiom: OWLSubClassOfAxiom ⇒ {
                buttons.add(
                  new TextMListButton(
                    "Accept",
                    Color.GREEN.darker(),
                    "\u2713",
                    14,
                    _ ⇒ {
                      //                      if (!repairedOntologyBecomesInconsistent(subClassOfAxiom)
                      //                        || userAnswersYes("<html>The repaired ontology becomes inconsistent if this axiom is added.<br>"
                      //                          + "Do you really want to accept it?"))
                      //                        answers.put(subClassOfAxiom, new AcceptAnswer())
                      if (repairedOntologyBecomesInconsistent(subClassOfAxiom))
                        showWarning("The repaired ontology becomes inconsistent if this axiom is added.")
                      else
                        answers.put(subClassOfAxiom, new AcceptAnswer())
                    }))
                buttons.add(
                  new TextMListButton(
                    "Ignore (accept but do not add it to the final result; use this option if the premise cannot be satisfied in the domain of interest, i.e., no counterexample can exist)",
                    Color.GRAY.darker(),
                    "?",
                    14,
                    _ ⇒ {
                      //                      if (!repairedOntologyBecomesInconsistent(subClassOfAxiom)
                      //                        || userAnswersYes("<html>The repaired ontology becomes inconsistent if this axiom is added.<br>"
                      //                          + "Do you really want to accept it?"))
                      //                        answers.put(subClassOfAxiom, new IgnoreAnswer())
                      if (repairedOntologyBecomesInconsistent(subClassOfAxiom))
                        showWarning("The repaired ontology becomes inconsistent if this axiom is added.")
                      else
                        answers.put(subClassOfAxiom, new IgnoreAnswer())
                    }))
                buttons.add(
                  new TextMListButton(
                    "Unsatisfiable Premise (experimental feature)",
                    Color.BLUE.darker(),
                    "\u22A5",
                    15,
                    _ ⇒ {
                      val unsatisfiableClassAxiom = getOWLDataFactory().getOWLSubClassOfAxiom(subClassOfAxiom.getSubClass(), ELConceptDescription.bot())
                      //                      if (!repairedOntologyBecomesInconsistent(unsatisfiableClassAxiom)
                      //                        || userAnswersYes("<html>The repaired ontology becomes inconsistent if this premise is declared as unsatisfiable.<br>"
                      //                          + "Do you really want to add the corresponding axiom?"))
                      //                        answers.put(subClassOfAxiom, new UnsatisfiablePremiseAnswer())
                      if (repairedOntologyBecomesInconsistent(unsatisfiableClassAxiom))
                        showWarning("The repaired ontology becomes inconsistent if this premise is declared as unsatisfiable.")
                      else
                        answers.put(subClassOfAxiom, new UnsatisfiablePremiseAnswer())
                    }))
                buttons.add(
                  new TextMListButton(
                    "Decline",
                    Color.RED.darker(),
                    "\u2715",
                    15,
                    _ ⇒ {
                      val counterexampleEditor = new OWLClassExpressionExpressionEditor()
                      counterexampleEditor.setup("", "", getOWLEditorKit())
                      counterexampleEditor.initialise()
                      counterexampleEditor.setDescription(subClassOfAxiom.getSubClass())
                      // JOptionPane.showOptionDialog(null, counterexampleEditor.getEditorComponent(), "", -1, 1, null, null, null)
                      val panel = new JPanel()
                      panel.setLayout(new GridLayout(0, 1))
                      panel.add(new JLabel("Please specify a counterexample against " + subClassOfAxiom + "!"))
                      panel.add(new JScrollPane(counterexampleEditor.getComponent()))
                      val indicator1 = new Label()
                      panel.add(indicator1)
                      val violatedAxiomListFrame = new AxiomListFrame(getOWLEditorKit())
                      val frameSection = violatedAxiomListFrame.getFrameSections().get(0)
                      val labelField = frameSection.getClass().getSuperclass().getDeclaredField("label")
                      labelField.setAccessible(true)
                      labelField.set(frameSection, "Violated Axioms")
                      val violatedAxiomList =
                        new OWLFrameList[java.util.Set[OWLAxiom]](getOWLEditorKit(), violatedAxiomListFrame) {
                          override protected def getButtons(value: Object): java.util.List[MListButton] = Collections.emptyList[MListButton]
                        }
                      val indicator2 = new Label()
                      panel.add(indicator2)
                      panel.add(violatedAxiomList)
                      val okButton = new JButton("OK")
                      val cancelButton = new JButton("Cancel")
                      val statusChangedListener: InputVerificationStatusChangedListener = state ⇒ {
                        if (counterexampleEditor.getClassExpressions() != null && !counterexampleEditor.getClassExpressions().isEmpty()) {
                          val classExpression = counterexampleEditor.getClassExpressions().iterator().next()
                          if (classExpression != null) {
                            val conceptDescription = new ELConceptDescription(classExpression)
                            val isCounterexample = conceptDescription.isSubsumedBy(new ELConceptDescription(subClassOfAxiom.getSubClass())) && !conceptDescription.isSubsumedBy(new ELConceptDescription(subClassOfAxiom.getSuperClass()))
                            val violatedConceptInclusions = Sets.newConcurrentHashSet[OWLAxiom]
                            repairedTBox.forEach(ci ⇒ {
                              if (conceptDescription.isSubsumedBy(ci.getSubsumee()) && !conceptDescription.isSubsumedBy(ci.getSubsumer()))
                                violatedConceptInclusions.add(ci.toOWLSubClassOfAxiom())
                            })
                            violatedAxiomList.setRootObject(violatedConceptInclusions)
                            violatedAxiomList.refreshComponent()
                            violatedAxiomList.repaint()
                            violatedAxiomList.validate()
                            okButton.setEnabled(isCounterexample && violatedConceptInclusions.isEmpty())
                            indicator1.setText("This is " + (if (isCounterexample) "" else "not ") + "a valid counterexample.")
                            if (violatedConceptInclusions.isEmpty())
                              indicator2.setText("")
                            else
                              indicator2.setText("The given counterexample violates the following axioms, which you have already confirmed as valid.<br>Please adjust the counterexample accordingly!")
                          } else {
                            okButton.setEnabled(false)
                            indicator1.setText("This is not a well-formed class expression.")
                            indicator2.setText("")
                          }
                        } else {
                          okButton.setEnabled(false)
                          indicator1.setText("This is not a well-formed class expression.")
                          indicator2.setText("")
                        }
                      }
                      counterexampleEditor.addStatusChangedListener(statusChangedListener)
                      val pane = new JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
                      okButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.OK_OPTION))
                      cancelButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.CANCEL_OPTION))
                      val dialog = pane.createDialog("New Counterexample")
                      dialog.setResizable(true)
                      dialog.setMinimumSize(new Dimension(400, 300))
                      dialog.setVisible(true)
                      if (pane.getValue().equals(JOptionPane.OK_OPTION)) {
                        val counterexample: OWLClassExpression = counterexampleEditor.getClassExpressions().iterator().next()
                        answers.put(subClassOfAxiom, new DeclineAnswer(counterexample))
                      }
                      counterexampleEditor.removeStatusChangedListener(statusChangedListener)
                      counterexampleEditor.dispose()
                      violatedAxiomList.dispose()
                      violatedAxiomListFrame.dispose()
                    }))
              }
              case subPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
                buttons.add(
                  new TextMListButton(
                    "Accept",
                    Color.GREEN.darker(),
                    "\u2713",
                    14,
                    _ ⇒ { answers.put(subPropertyChainOfAxiom, new AcceptAnswer()) }))
                buttons.add(
                  new TextMListButton(
                    "Decline",
                    Color.RED.darker(),
                    "\u2715",
                    15,
                    _ ⇒ { answers.put(subPropertyChainOfAxiom, new DeclineAnswerWithoutCounterexample()) }))
              }
            }
            buttons
          } else
            Collections.emptyList()
        }
      }
    counterexampleAxiomList.setRootObject(Collections.emptySet())
    confirmedAxiomList.setRootObject(Collections.emptySet())
    pendingAxiomList.setRootObject(questions)
    setLayout(new BorderLayout())
    repairButton = new Button("Repair...")
    repairButton.addActionListener(repairButtonActionListener_Start)
    val topPanel = new JPanel()
    topPanel.setLayout(new BorderLayout())
    topPanel.add(repairButton, BorderLayout.EAST)
    add(topPanel, BorderLayout.NORTH)
    val listPanel = new JPanel()
    listPanel.setLayout(new GridLayout(3, 1))
    listPanel.add(new JScrollPane(counterexampleAxiomList))
    listPanel.add(new JScrollPane(confirmedAxiomList))
    listPanel.add(new JScrollPane(pendingAxiomList))
    add(listPanel, BorderLayout.CENTER)
    val bottomPanel = new JPanel()
    bottomPanel.setLayout(new BorderLayout())
    statusLabel = new Label()
    bottomPanel.add(statusLabel, BorderLayout.CENTER)
    add(bottomPanel, BorderLayout.SOUTH)
    println("TBox Exploration View Component successfully initialized.")
  }

  protected def disposeOWLView() {
    counterexampleAxiomList.dispose()
    counterexampleAxiomListFrame.dispose()
    confirmedAxiomList.dispose()
    confirmedAxiomListFrame.dispose()
    pendingAxiomList.dispose()
    pendingAxiomListFrame.dispose()
    questions.clear()
    answers.clear()
    counterexamples.clear()
    repairedTBox.clear()
    ignoredTBox.clear()
    confirmedRoleIncompatibilityAxioms.clear()
    checkedBinaryRoleCompositions.clear()
  }

  private def startRepairThread() {
    thread = new Thread(() ⇒ repair())
    thread.start()
  }

  private def stopRepairThread() {
    if (thread != null) { // Implement a more elegant way to stop the repairing process
      thread.stop()
      cleanup()
      println("Repair cancelled.")
      setStatus("Repair cancelled.")
    }
  }

  private val rankCache = new ConcurrentHashMap[ELConceptDescription, Long]
  private def cachedRank(conceptDescription: ELConceptDescription): Long = {
    if (rankCache containsKey conceptDescription)
      rankCache get conceptDescription
    else {
      val rank = conceptDescription.rank5()
      rankCache put (conceptDescription, rank)
      rank
    }
  }

  private def repair() {
    Util.runOnProtegeThread(() ⇒ {
      println("Starting repair...")
      setStatus("Starting repair...")
      //    repairButton.setEnabled(false)
      repairButton.removeActionListener(repairButtonActionListener_Start)
      repairButton.setLabel("Stop Repair")
      repairButton.addActionListener(repairButtonActionListener_Stop)
    }, true)
    questions.clear()
    answers.clear()
    futures.clear()
    repairedTBox.clear()
    ignoredTBox.clear()
    confirmedRoleIncompatibilityAxioms.clear()
    checkedBinaryRoleCompositions.clear()
    counterexamples.clear()
    counterexampleInterpretation = new ELInterpretation2[ELConceptDescription]

    val roleDepth = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal role depth", 2))
    val maxRank = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal rank", 16))
    val exploreRoleIncompatibilityAxioms =
      !userAnswersYes(
        "<html>Is the ontology complete for role incompatibility axioms?<br>" +
          "If you select 'No', then you will be asked whether some binary<br>" +
          "role compositions are unsatisfiable.  Note that this is an<br>" +
          "experimental feature.")

    val activeOntology = getOWLModelManager().getActiveOntology()
    val activeOntologyIRI = if (activeOntology.getOntologyID().getOntologyIRI().get() == null) "" else activeOntology.getOntologyID().getOntologyIRI().get().toString()

    val canonicalModelOfABox = getCanonicalModelOfABox(activeOntology)
    val _refutableTBox = activeOntology.getTBoxAxioms(Imports.EXCLUDED)
    val (refutableTBox, rangeRestrictions) = transformTBox(_refutableTBox)
    println("refutable TBox: " + refutableTBox)
    val signature = new Signature(IRI.create(""))
    var j = -1
    val namedIndividuals = Sets.newConcurrentHashSet[OWLNamedIndividual]
    activeOntology.getSignature().forEach({
      case owlClass: OWLClass ⇒ {
        if (!owlClass.isBuiltIn()) {
          counterexampleInterpretation.synchronized {
            counterexampleInterpretation.getConceptNameExtensionMatrix().colHeads().add(owlClass.getIRI())
          }
          signature.addConceptNames(owlClass.getIRI())
        }
      }
      case owlObjectProperty: OWLObjectProperty ⇒ {
        if (!owlObjectProperty.isBuiltIn()) {
          signature.addRoleNames(owlObjectProperty.getIRI())
        }
      }
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
    println("signature: " + signature)

    for (namedIndividual ← namedIndividuals.asScala) {
      val c = canonicalModelOfABox.getMostSpecificConceptDescription(namedIndividual, roleDepth)
      newCounterexample(c, namedIndividual)
    }
    updateProvidedCounterexamples()

    val clopConfirmedRoleIncompatibilityAxioms = clopFromTBox(confirmedRoleIncompatibilityAxioms, roleDepth)
    val clopRepairedTBox = clopFromTBox(repairedTBox, roleDepth)
    val clopRefutableTBox =
      compose(
        clopFromTBox(refutableTBox, roleDepth),
        clopConfirmedRoleIncompatibilityAxioms)
    //    val clopOnlyCounterexamples: DualClosureOperator[ELConceptDescription] =
    //      concept ⇒ {
    //        if (concept.isBot())
    //          concept.clone().reduce()
    //        else
    //          counterexampleInterpretation.getMostSpecificConceptDescription(Sets.intersection(counterexampleInterpretation.getExtension(concept), counterexamples.keySet()), rd)
    //      }
    //    val clopCounterexamples =
    //      compose(
    //        compatibilize(clopOnlyCounterexamples, rd),
    //        clopConfirmedRoleIncompatibilityAxioms)
    val clopCounterexamples: DualClosureOperator[ELConceptDescription] =
      concept ⇒ {
        if (concept.isBot())
          concept.clone().reduce()
        else
          counterexampleInterpretation.synchronized {
            counterexampleInterpretation.getMostSpecificConceptDescription(Sets.intersection(counterexampleInterpretation.getExtension(concept), counterexamples.keySet()), roleDepth)
          }
      }
    val clopRefutableTBoxAndCounterexamples = DualClosureOperator.infimum(clopRefutableTBox, clopCounterexamples)

    val candidates = Sets.newConcurrentHashSet[ELConceptDescription]
    candidates.add(ELConceptDescription.top())
    var rank: Long = 0

    def containsUnsatisfiableBinaryRoleComposition(conceptDescription: ELConceptDescription): Boolean = {
      var containsUnsatisfiableBinaryRoleComposition = false
      val uncheckedBinaryRoleCompositionsInCandidate = getAllBinaryRoleCompositionsIn(conceptDescription)
      uncheckedBinaryRoleCompositionsInCandidate.removeAll(checkedBinaryRoleCompositions)
      uncheckedBinaryRoleCompositionsInCandidate.parallelStream().forEach({
        case (role1, role2) ⇒ {
          val question = getOWLDataFactory().getOWLSubPropertyChainOfAxiom(
            Lists.newArrayList(
              getOWLDataFactory().getOWLObjectProperty(role1),
              getOWLDataFactory().getOWLObjectProperty(role2)),
            getOWLDataFactory().getOWLBottomObjectProperty())
          val future = askExpert(question, counterexamples.size())
          val answer = future.get()
          questions.remove(question)
          Util.runOnProtegeThread(() ⇒ { pendingAxiomList.setRootObject(questions) }, true)
          answer match {
            case AcceptAnswer() ⇒ {
              val roleIncompatibilityAxiom =
                new ELConceptInclusion(
                  ELConceptDescription.existentialRestriction(
                    role1,
                    ELConceptDescription.existentialRestriction(
                      role2,
                      ELConceptDescription.top())),
                  ELConceptDescription.bot())
              repairedTBox.add(roleIncompatibilityAxiom)
              //                        refutableTBox.add(roleIncompatibilityAxiom)
              confirmedRoleIncompatibilityAxioms.add(roleIncompatibilityAxiom)
              containsUnsatisfiableBinaryRoleComposition = true
              updateConfirmedAxioms()
            }
            case DeclineAnswerWithoutCounterexample() ⇒ {}
            case InheritedDeclineAnswer()             ⇒ {}
          }
          checkedBinaryRoleCompositions add (role1, role2)
        }
      })
      containsUnsatisfiableBinaryRoleComposition
    }

    def processCandidate(candidate: ELConceptDescription) {
      var message = "candidate: " + candidate + " from thread " + Thread.currentThread().toString()
      val closureRepairedTBox = clopRepairedTBox(candidate).reduce()
      message += "\r\n  with closure (repaired TBox): " + closureRepairedTBox
      if (!closureRepairedTBox.isBot()) {
        if (candidate.isEquivalentTo(closureRepairedTBox)) {
          if (!(exploreRoleIncompatibilityAxioms && containsUnsatisfiableBinaryRoleComposition(candidate))) {
            var closureRefutableTBoxAndCounterexamples = clopRefutableTBoxAndCounterexamples(candidate).reduce()
            message += "\r\n  with closure (refutable TBox and counterexamples): " + closureRefutableTBoxAndCounterexamples
            message += "\r\n  with closure (refutable TBox): " + clopRefutableTBox(candidate).reduce()
            message += "\r\n  with closure (counterexamples): " + clopCounterexamples(candidate).reduce()
            println(message)
            if (exploreRoleIncompatibilityAxioms && containsUnsatisfiableBinaryRoleComposition(closureRefutableTBoxAndCounterexamples)) {
              if (!clopRefutableTBoxAndCounterexamples(candidate).reduce().isBot()) throw new RuntimeException()
              closureRefutableTBoxAndCounterexamples = ELConceptDescription.bot()
            }
            var ask = !candidate.isEquivalentTo(closureRefutableTBoxAndCounterexamples)
            var ignore = false
            var unsatisfiablePremise = false
            while (ask) {
              ask = false
              val question = new ELConceptInclusion(candidate, closureRefutableTBoxAndCounterexamples without candidate).toOWLSubClassOfAxiom()
              val future = askExpert(question, counterexamples.size())
              val answer = future.get()
              questions.remove(question)
              Util.runOnProtegeThread(() ⇒ { pendingAxiomList.setRootObject(questions) }, true)
              answer match {
                case AcceptAnswer()               ⇒ {}
                case IgnoreAnswer()               ⇒ { ignore = true }
                case UnsatisfiablePremiseAnswer() ⇒ { unsatisfiablePremise = true }
                case DeclineAnswer(counterexample) ⇒ {
                  val c = new ELConceptDescription(counterexample)
                  newCounterexample(c, getOWLDataFactory().getOWLNamedIndividual(IRI.create(activeOntologyIRI + "#counterexample-" + nextCounterexampleNumber.getAndIncrement())))
                  updateProvidedCounterexamples()
                  closureRefutableTBoxAndCounterexamples = clopRefutableTBoxAndCounterexamples(candidate).reduce()
                  println("  new counterexample: " + c
                    + "\r\n  updated closure (refutable TBox and counterexamples): " + closureRefutableTBoxAndCounterexamples
                    + "\r\n  updated closure (refutable TBox): " + clopRefutableTBox(candidate).reduce()
                    + "\r\n  updated closure (counterexamples): " + clopCounterexamples(candidate).reduce())
                  ask = !candidate.isEquivalentTo(closureRefutableTBoxAndCounterexamples)
                }
                case InheritedDeclineAnswer() ⇒ {
                  closureRefutableTBoxAndCounterexamples = clopRefutableTBoxAndCounterexamples(candidate).reduce()
                  println("  updated closure (refutable TBox and counterexamples): " + closureRefutableTBoxAndCounterexamples
                    + "\r\n  updated closure (refutable TBox): " + clopRefutableTBox(candidate).reduce()
                    + "\r\n  updated closure (counterexamples): " + clopCounterexamples(candidate).reduce())
                  ask = !candidate.isEquivalentTo(closureRefutableTBoxAndCounterexamples)
                }
              }
            }
            if (unsatisfiablePremise) {
              repairedTBox.add(new ELConceptInclusion(candidate, ELConceptDescription.bot()))
              updateConfirmedAxioms()
            } else {
              closureRefutableTBoxAndCounterexamples = clopRefutableTBoxAndCounterexamples(candidate).reduce()
              if (!candidate.isEquivalentTo(closureRefutableTBoxAndCounterexamples)) {
                val ci = new ELConceptInclusion(candidate, closureRefutableTBoxAndCounterexamples without candidate)
                repairedTBox.add(ci)
                if (ignore) ignoredTBox.add(ci)
                updateConfirmedAxioms()
              }
              closureRefutableTBoxAndCounterexamples.lowerNeighborsB(signature).forEach(lowerNeighbor ⇒
                candidates.add(lowerNeighbor.reduce()))
            }
          }
        } else {
          if (!closureRepairedTBox.isBot())
            candidates.add(closureRepairedTBox)
          println(message)
        }
      } else {
        println(message)
      }
    }

    while (rank <= maxRank && !candidates.isEmpty()) {
      println("rank: " + rank)
      setStatus("rank: " + rank)
      println("repaired TBox: " + repairedTBox)
      println("counterexamples: " + counterexamples)
      candidates.retainAll(Collections3.representatives(candidates, ELConceptDescription.equivalence()))
      val currentCandidates = candidates.parallelStream().filter(cachedRank(_) == rank).collect(Collectors.toSet())
      println("all candidates: " + candidates)
      println("current candidates: " + currentCandidates)
      candidates.removeAll(currentCandidates)
      currentCandidates.parallelStream().forEach(
        candidate ⇒ if (candidate.roleDepth() <= roleDepth) processCandidate(candidate))
      //      rank += 1
      rank = candidates.parallelStream().map[Long](cachedRank).min(java.lang.Long.compare).orElse(rank + 1)
    }
    println("Repair finished.")
    setStatus("Repair finished.")

    println("Writing changes to ontology...")
    Util.runOnProtegeThread(() ⇒ { getOWLModelManager().getOWLOntologyManager().removeAxioms(getOWLModelManager().getActiveOntology, _refutableTBox) }, true)
    println("Removed old concept inclusions.")
    val _repairedTBox = Sets.newHashSet[OWLAxiom]
    repairedTBox.removeAll(ignoredTBox)
    repairedTBox.forEach(conceptInclusion ⇒
      _repairedTBox.add(conceptInclusion.toOWLSubClassOfAxiom()))
    println("Now adding new concept inclusions...")
    Util.runOnProtegeThread(() ⇒ { getOWLModelManager().getOWLOntologyManager().addAxioms(getOWLModelManager().getActiveOntology, _repairedTBox) }, true)
    val providedCounterexamples = Sets.newHashSet[OWLAxiom]
    counterexamples.entrySet().forEach(counterexample ⇒
      providedCounterexamples.add(getOWLDataFactory().getOWLClassAssertionAxiom(counterexample.getKey().toOWLClassExpression(), counterexample.getValue())))
    println("Now adding counterexamples...")
    Util.runOnProtegeThread(() ⇒ { getOWLModelManager().getOWLOntologyManager().addAxioms(getOWLModelManager().getActiveOntology, providedCounterexamples) }, true)
    println("Changes successfully written to ontology.")
    cleanup()
  }

  private abstract class Answer {}
  private case class AcceptAnswer() extends Answer {}
  private case class IgnoreAnswer() extends Answer {}
  private case class UnsatisfiablePremiseAnswer() extends Answer {}
  private case class DeclineAnswer(val counterexample: OWLClassExpression) extends Answer {}
  private case class InheritedDeclineAnswer() extends Answer {}
  private case class DeclineAnswerWithoutCounterexample() extends Answer {}

  private def askExpert(question: OWLAxiom, counter: Integer): Future[Answer] = synchronized {
    println("*** new question: " + question)
    questions.add(question)
    Util.runOnProtegeThread(() ⇒ {
      pendingAxiomList.setRootObject(questions)
      pendingAxiomList.refreshComponent()
      pendingAxiomList.repaint()
      pendingAxiomList.validate()
    }, true)
    if (futures.containsKey((question, counter)))
      futures.get((question, counter))
    else {
      val future = new Future[Answer]() {
        private var answer: Answer = null
        override def cancel(mayInterruptIfRunning: Boolean): Boolean = throw new RuntimeException("Not supported")
        override def isCancelled(): Boolean = false
        override def isDone(): Boolean = synchronized { answer != null || answers.containsKey(question) }

        private def tryGetAnswer() {
          synchronized {
            if (answer == null) {
              answer = answers.get(question)
              answers.remove(question)
            }
          }
        }

        @throws(classOf[InterruptedException])
        @throws(classOf[ExecutionException])
        override def get(): Answer = {
          while (!isDone())
            Thread.sleep(100)
          tryGetAnswer()
          answer
        }

        @throws(classOf[InterruptedException])
        @throws(classOf[ExecutionException])
        @throws(classOf[TimeoutException])
        override def get(timeout: Long, unit: TimeUnit): Answer = {
          val maxWaitTime = unit.toMillis(timeout)
          var curWaitTime = 0
          while (!isDone()) {
            Thread.sleep(100)
            curWaitTime += 100
            if (curWaitTime >= maxWaitTime)
              throw new TimeoutException
          }
          tryGetAnswer()
          answer
        }
      }
      futures.put((question, counter), future)
      future
    }
  }

  private implicit def toOWLClassExpression(conceptDescription: ELConceptDescription): OWLClassExpression = {
    conceptDescription.toOWLClassExpression()
  }

  private implicit def toELConceptDescription(classExpression: OWLClassExpression): ELConceptDescription = {
    new ELConceptDescription(classExpression)
  }

  private def setStatus = statusLabel.setText(_)

  private def repairedOntologyBecomesInconsistent(axiom: OWLAxiom): Boolean = {
    axiom match {
      case owlSubClassOfAxiom: OWLSubClassOfAxiom ⇒ {
        val newCI = new ELConceptInclusion(owlSubClassOfAxiom)
        val newRepairedTBox = new java.util.HashSet(repairedTBox)
        newRepairedTBox add newCI
        clopFromTBox(newRepairedTBox, 0)(ELConceptDescription.top()).isBot() ||
          counterexamples.keySet().parallelStream().anyMatch(counterexample ⇒
            clopFromTBox(newRepairedTBox, counterexample.roleDepth())(counterexample).isBot())
      }
      case owlSubPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
        false
      }
    }
  }

  private def userAnswersYes(question: String): Boolean = {
    JOptionPane.showConfirmDialog(
      null,
      new JLabel(question),
      UIManager.getString("OptionPane.confirmDialogTitle", null),
      JOptionPane.YES_NO_OPTION,
      JOptionPane.QUESTION_MESSAGE) == 0
  }

  private def showWarning(message: String) {
    JOptionPane.showMessageDialog(
      null,
      new JLabel(message),
      UIManager.getString("OptionPane.messageDialogTitle", null),
      JOptionPane.WARNING_MESSAGE)
  }

  private def updateProvidedCounterexamples() {
    val providedCounterexamples = Sets.newHashSet[OWLAxiom]
    counterexamples.entrySet().forEach(counterexample ⇒
      providedCounterexamples.add(getOWLDataFactory().getOWLClassAssertionAxiom(counterexample.getKey().toOWLClassExpression(), counterexample.getValue())))
    Util.runOnProtegeThread(() ⇒ {
      counterexampleAxiomList.setRootObject(providedCounterexamples)
      counterexampleAxiomList.refreshComponent()
      counterexampleAxiomList.repaint()
      counterexampleAxiomList.validate()
    }, true)
  }

  private def updateConfirmedAxioms() {
    val confirmedAxioms = Sets.newHashSet[OWLAxiom]
    repairedTBox.forEach(conceptInclusion ⇒
      if (!ignoredTBox.contains(conceptInclusion))
        confirmedAxioms.add(conceptInclusion.toOWLSubClassOfAxiom()))
    Util.runOnProtegeThread(() ⇒ {
      confirmedAxiomList.setRootObject(confirmedAxioms)
      confirmedAxiomList.refreshComponent()
      confirmedAxiomList.repaint()
      confirmedAxiomList.validate()
    }, true)
  }

  private def clearPendingAxioms() {
    Util.runOnProtegeThread(() ⇒ {
      pendingAxiomList.setRootObject(Collections.emptySet())
      pendingAxiomList.refreshComponent()
      pendingAxiomList.repaint()
      pendingAxiomList.validate()
    }, true)
  }

  private def cleanup() {
    println("Cleaning up...")
    counterexamples.clear()
    repairedTBox.clear()
    ignoredTBox.clear()
    confirmedRoleIncompatibilityAxioms.clear()
    checkedBinaryRoleCompositions.clear()
    questions.clear()
    answers.clear()
    futures.clear()
    updateProvidedCounterexamples()
    updateConfirmedAxioms()
    clearPendingAxioms()
    println("Everything done.")
    Util.runOnProtegeThread(() ⇒ {
      //        repairButton.setEnabled(true)
      repairButton.setLabel("Repair...")
      repairButton.removeActionListener(repairButtonActionListener_Stop)
      repairButton.addActionListener(repairButtonActionListener_Start)
    }, true)
  }

  private def newCounterexample(counterexample: ELConceptDescription, individual: OWLNamedIndividual) {
    val n = counterexamples.size()
    insertCounterexample(counterexample)
    counterexamples.put(counterexample, individual)
    checkedBinaryRoleCompositions addAll getAllBinaryRoleCompositionsIn(counterexample)
    questions.forEach({
      case owlSubClassOfAxiom: OWLSubClassOfAxiom ⇒ {
        val ci = new ELConceptInclusion(owlSubClassOfAxiom)
        if ((counterexample isSubsumedBy ci.getSubsumee()) && !(counterexample isSubsumedBy ci.getSubsumer()))
          answers.put(owlSubClassOfAxiom, new InheritedDeclineAnswer())
      }
      case owlSubPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
        if (checkedBinaryRoleCompositions contains (
          owlSubPropertyChainOfAxiom.getPropertyChain().get(0).asOWLObjectProperty().getIRI(),
          owlSubPropertyChainOfAxiom.getPropertyChain().get(1).asOWLObjectProperty().getIRI()))
          answers.put(owlSubPropertyChainOfAxiom, new InheritedDeclineAnswer())
      }
    })
  }

  private def insertCounterexample(c: ELConceptDescription) {
    counterexampleInterpretation.synchronized {
      //        counterexamples.getDomain().add(c)
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

  private def getCanonicalModelOfABox(ontology: OWLOntology): ELInterpretation2[OWLIndividual] = {
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
        val targetIndividual = getOWLDataFactory().getOWLAnonymousIndividual(NodeID.nextAnonymousIRI())
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

  private def transformTBox(ontology: java.util.Set[OWLAxiom]): (java.util.Set[ELConceptInclusion], java.util.Map[IRI, ELConceptDescription]) = {
    val refutableTBox = Sets.newConcurrentHashSet[ELConceptInclusion]
    val rangeRestrictions = new ConcurrentHashMap[IRI, ELConceptDescription]()
    ontology.forEach(axiom ⇒ {
      axiom.getAxiomType() match {
        case AxiomType.SUBCLASS_OF ⇒ {
          val subClassOfAxiom = axiom.asInstanceOf[OWLSubClassOfAxiom]
          try {
            refutableTBox.add(new ELConceptInclusion(new ELConceptDescription(subClassOfAxiom.getSubClass()).reduce(), new ELConceptDescription(subClassOfAxiom.getSuperClass()).reduce()))
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
                refutableTBox.add(
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
              refutableTBox.add(
                new ELConceptInclusion(
                  new ELConceptDescription(equivalentClasses.get(i - 1)),
                  new ELConceptDescription(equivalentClasses.get(i))))
            } catch {
              case _: ELSyntaxException ⇒ { println("cannot handle " + axiom) }
            }
          })
          try {
            refutableTBox.add(
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
              refutableTBox.add(
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
    (refutableTBox, rangeRestrictions)
  }

  private def addAllBinaryRoleCompositions(conceptDescription: ELConceptDescription, binaryRoleCompositions: java.util.Set[(IRI, IRI)]) {
    conceptDescription.getExistentialRestrictions().entries().forEach(entry ⇒ {
      val role1 = entry.getKey()
      val fillerConceptDescription = entry.getValue()
      fillerConceptDescription.getExistentialRestrictions().keySet().forEach(role2 ⇒ {
        binaryRoleCompositions add (role1, role2)
      })
    })
  }

  private def getAllBinaryRoleCompositionsIn(conceptDescription: ELConceptDescription): java.util.Set[(IRI, IRI)] = {
    val binaryRoleCompositions = Sets.newConcurrentHashSet[(IRI, IRI)]
    addAllBinaryRoleCompositions(conceptDescription, binaryRoleCompositions)
    binaryRoleCompositions
  }

  private def compatibilize(clop: DualClosureOperator[ELConceptDescription], roleDepth: Int): DualClosureOperator[ELConceptDescription] = concept ⇒ {
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

  private def clopFromTBox(tBox: java.util.Set[ELConceptInclusion], roleDepth: Int): DualClosureOperator[ELConceptDescription] = concept ⇒ {
    if (roleDepth < 0)
      throw new IllegalArgumentException("Role depth cannot be smaller than 0.")
    else if (concept.roleDepth() > roleDepth)
      throw new IllegalArgumentException("The role depth of the concept description exceeds the given role depth.")
    else if (concept.isBot())
      concept.clone().reduce()
    else {
      val _tbox: Set[(ELsiConceptDescription[Integer], ELsiConceptDescription[Integer])] =
        Set.empty ++ tBox.asScala.map(ci ⇒
          (ELsiConceptDescription.of(ci.getSubsumee()), ELsiConceptDescription.of(ci.getSubsumer())))
      ELsiConceptDescription.of(concept).clone().mostSpecificConsequence(_tbox).approximate(roleDepth)
    }
  }
  private def compose(clop1: DualClosureOperator[ELConceptDescription], clop2: DualClosureOperator[ELConceptDescription]): DualClosureOperator[ELConceptDescription] =
    concept ⇒ clop2(clop1(concept))

  private def reduceTBox(conceptDescription: ELConceptDescription, conceptInclusions: Set[ELConceptInclusion]): ELConceptDescription = {
    val reduction = conceptDescription.clone().reduce()

    reduction
  }

}
