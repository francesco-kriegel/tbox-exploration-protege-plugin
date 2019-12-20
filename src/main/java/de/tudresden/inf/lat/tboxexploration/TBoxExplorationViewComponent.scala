package de.tudresden.inf.lat.tboxexploration

import java.awt.BorderLayout
import java.awt.Button
import java.awt.Color
import java.awt.Dimension
import java.awt.Graphics2D
import java.awt.GridLayout
import java.util.Collections
import java.util.Optional
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
import org.protege.editor.owl.ui.editor.OWLClassExpressionExpressionEditor
import org.protege.editor.owl.ui.frame.AxiomListFrame
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.protege.editor.owl.ui.view.AbstractOWLViewComponent
import org.semanticweb.owlapi.model.AxiomType
import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLNamedIndividual
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.parameters.Imports

import com.google.common.collect.Sets

import conexp.fx.core.dl.ELConceptDescription
import conexp.fx.core.dl.ELConceptInclusion
import conexp.fx.core.dl.ELInterpretation2
import conexp.fx.core.dl.ELTBox
import conexp.fx.core.dl.ELsiConceptDescription
import conexp.fx.core.dl.Signature
import conexp.fx.core.math.DualClosureOperator
import javax.swing.JButton
import javax.swing.JLabel
import javax.swing.JOptionPane
import javax.swing.JPanel
import javax.swing.JScrollPane
import java.awt.Label

class TBoxExplorationViewComponent extends AbstractOWLViewComponent {

  protected def disposeOWLView() {
    pendingAxiomList.dispose()
    pendingAxiomListFrame.dispose()
    questions.clear()
    answers.clear()
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
            val frameRow: OWLFrameSectionRow[_, OWLAxiom, _] = value.asInstanceOf[OWLFrameSectionRow[_, OWLAxiom, _]];
            val axiom = frameRow.getAxiom().asInstanceOf[OWLSubClassOfAxiom]
            val buttons = new java.util.ArrayList[MListButton]
            buttons.add(new MListButton("Accept", Color.GREEN.darker(), _ ⇒ {
              answers.put(axiom, new AcceptAnswer())
              questions.remove(axiom)
              pendingAxiomList.setRootObject(questions)
            }) {
              def paintButtonContent(g: Graphics2D) {}
            })
            buttons.add(new MListButton("Ignore", Color.GRAY.darker(), _ ⇒ {
              answers.put(axiom, new IgnoreAnswer())
              questions.remove(axiom)
              pendingAxiomList.setRootObject(questions)
            }) {
              def paintButtonContent(g: Graphics2D) {}
            })
            buttons.add(new MListButton("Unsatisfiable Premise", Color.YELLOW.darker(), _ ⇒ {
              answers.put(axiom, new UnsatisfiablePremiseAnswer())
              questions.remove(axiom)
              pendingAxiomList.setRootObject(questions)
            }) {
              def paintButtonContent(g: Graphics2D) {}
            })
            buttons.add(new MListButton("Decline", Color.RED.darker(), _ ⇒ {
              val counterexampleEditor = new OWLClassExpressionExpressionEditor()
              counterexampleEditor.setup("", "", getOWLEditorKit())
              counterexampleEditor.initialise()
              counterexampleEditor.setDescription(axiom.getSubClass())
              // JOptionPane.showOptionDialog(null, counterexampleEditor.getEditorComponent(), "", -1, 1, null, null, null)
              val panel = new JPanel()
              panel.setLayout(new GridLayout(0, 1))
              panel.add(new JLabel("Please specify a counterexample against " + axiom + "!"))
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
              counterexampleEditor.addStatusChangedListener(state ⇒ {
                if (counterexampleEditor.getClassExpressions() != null && !counterexampleEditor.getClassExpressions().isEmpty()) {
                  val classExpression = counterexampleEditor.getClassExpressions().iterator().next()
                  if (classExpression != null) {
                    val conceptDescription = new ELConceptDescription(classExpression)
                    val isCounterexample = conceptDescription.isSubsumedBy(new ELConceptDescription(axiom.getSubClass())) && !conceptDescription.isSubsumedBy(new ELConceptDescription(axiom.getSuperClass()))
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
              })
              val pane = new JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
              okButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.OK_OPTION))
              cancelButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.CANCEL_OPTION))
              val dialog = pane.createDialog("New Counterexample")
              dialog.setResizable(true)
              dialog.setMinimumSize(new Dimension(400, 300))
              dialog.setVisible(true)
              if (pane.getValue().equals(JOptionPane.OK_OPTION)) {
                val counterexample: OWLClassExpression = counterexampleEditor.getClassExpressions().iterator().next()
                answers.put(axiom, new DeclineAnswer(counterexample))
                questions.remove(axiom)
                pendingAxiomList.setRootObject(questions)
              }
            }) {
              def paintButtonContent(g: Graphics2D) {}
            })
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
    repairButton.addActionListener(_ ⇒ startRepair())
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

  private val counterexamples = new ConcurrentHashMap[ELConceptDescription, OWLNamedIndividual]
  private val nextCounterexampleNumber = new AtomicInteger(0)
  private val repairedTBox = Sets.newConcurrentHashSet[ELConceptInclusion]

  private def startRepair() {
    println("Starting repair...")
    setStatus("Starting repair...")
    repairButton.setEnabled(false)
    questions.clear()
    answers.clear()
    val rd = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal role depth", 2))
    val maxRank = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal rank", 16))
    val activeOntology = getOWLModelManager().getActiveOntology()
    val activeOntologyIRI = if (activeOntology.getOntologyID().getOntologyIRI().get() == null) "" else activeOntology.getOntologyID().getOntologyIRI().get().toString()
    var j = -1
    activeOntology.getSignature().forEach(entity ⇒ {
      if (entity.isOWLNamedIndividual()) {
        val name = entity.asOWLNamedIndividual().getIRI().toString().replaceFirst(activeOntologyIRI + "#counterexample-", "")
        try {
          val i = Integer.valueOf(name)
          j = Math.max(j, i)
        } catch { case _: NumberFormatException ⇒ {} }
      }
    })
    nextCounterexampleNumber.set(j + 1)
    val _refutableTBox = activeOntology.getTBoxAxioms(Imports.EXCLUDED)
    val refutableTBox = new ELTBox()
    _refutableTBox.forEach(axiom ⇒ {
      if (axiom.getAxiomType().equals(AxiomType.SUBCLASS_OF)) {
        val subClassOfAxiom: OWLSubClassOfAxiom = axiom.asInstanceOf[OWLSubClassOfAxiom]
        refutableTBox.getConceptInclusions().add(new ELConceptInclusion(new ELConceptDescription(subClassOfAxiom.getSubClass()).reduce(), new ELConceptDescription(subClassOfAxiom.getSuperClass()).reduce()))
      }
    })
    println("refutable TBox: " + refutableTBox)
    //    val signature = refutableTBox.getSignature()
    val signature = new Signature(IRI.create(""))
    getOWLModelManager().getActiveOntology.getSignature.forEach(entity ⇒ {
      if (entity.isOWLClass() && !entity.asOWLClass().isOWLThing() && !entity.asOWLClass().isOWLNothing())
        signature.addConceptNames(entity.asOWLClass().getIRI())
      else if (entity.isOWLObjectProperty())
        signature.addRoleNames(entity.asOWLObjectProperty().getIRI())
    })
    println("signature: " + signature)
    println("Starting thread...")
    new Thread(() ⇒ {
      repairedTBox.clear()
      val candidates = Sets.newConcurrentHashSet[ELConceptDescription]
      val counterexampleInterpretation = new ELInterpretation2[ELConceptDescription]
      counterexamples.clear()
      def insertCounterexample(c: ELConceptDescription) {
        //        counterexamples.getDomain().add(c)
        counterexampleInterpretation.getConceptNameExtensionMatrix().rowHeads().add(c)
        counterexampleInterpretation.getConceptNameExtensionMatrix().colHeads().addAll(c.getConceptNames())
        counterexampleInterpretation.getConceptNameExtensionMatrix().row(c).addAll(c.getConceptNames())
        c.getExistentialRestrictions().entries().forEach(entry ⇒ {
          insertCounterexample(entry.getValue())
          counterexampleInterpretation.getRoleNameExtensionMatrix(entry.getKey()).add(c, entry.getValue())
        })
      }

      val clop = DualClosureOperator.infimum((concept: ELConceptDescription) ⇒ {
        if (rd < 0 || concept.roleDepth() > rd)
          throw new IllegalArgumentException()
        else if (concept.isBot())
          concept.clone().reduce()
        else {
          val _tbox: Set[Pair[ELsiConceptDescription[Integer], ELsiConceptDescription[Integer]]] =
            Set.empty ++ refutableTBox.getConceptInclusions().asScala.map(ci ⇒
              (ELsiConceptDescription.of(ci.getSubsumee()), ELsiConceptDescription.of(ci.getSubsumer())))
          ELsiConceptDescription.of(concept).clone().mostSpecificConsequence(_tbox).approximate(rd)
        }
      }, new DualClosureOperator[ELConceptDescription]() {
        def closure(concept: ELConceptDescription): ELConceptDescription = {
          if (concept.isBot())
            concept.clone().reduce()
          else
            counterexampleInterpretation.getMostSpecificConceptDescription(Sets.intersection(counterexampleInterpretation.getExtension(concept), counterexamples.keySet()), rd)
        }
      })
      val clop2: DualClosureOperator[ELConceptDescription] = concept ⇒ {
        if (rd < 0 || concept.roleDepth() > rd)
          throw new IllegalArgumentException()
        else if (concept.isBot())
          concept.clone().reduce()
        else {
          val _tbox: Set[Pair[ELsiConceptDescription[Integer], ELsiConceptDescription[Integer]]] =
            Set.empty ++ repairedTBox.asScala.map(ci ⇒
              (ELsiConceptDescription.of(ci.getSubsumee()), ELsiConceptDescription.of(ci.getSubsumer())))
          ELsiConceptDescription.of(concept).clone().mostSpecificConsequence(_tbox).approximate(rd)
          //        val tbox = new ELTBox()
          //        tbox.getConceptInclusions().addAll(repairedTBox)
          //        tbox.getMostSpecificConsequence(concept, rd)
        }
      }

      candidates.add(ELConceptDescription.top())
      //      val pool = Executors.newWorkStealingPool()
      var rank = 0
      //      var go = true
      //      while (go) {
      while (rank <= maxRank) {
        println("rank: " + rank)
        setStatus("rank: " + rank)
        println("repaired TBox: " + repairedTBox)
        println("counterexamples: " + counterexamples)
        val currentCandidates = candidates.parallelStream().filter(_.rank() == rank).collect(Collectors.toSet())
        //        var minRD = Integer.MAX_VALUE
        //        candidates.forEach(c ⇒ { minRD = Math.min(minRD, c.roleDepth()) })
        //        go = minRD <= rd
        //        val futures = Sets.newConcurrentHashSet[Future[_]]
        //        currentCandidates.parallelStream().forEach(candidate ⇒ if (candidate.roleDepth() <= rd) futures.add(pool.submit(() ⇒ {
        println("all candidates: " + candidates)
        println("current candidates: " + currentCandidates)
        candidates.removeAll(currentCandidates)
        currentCandidates.parallelStream().forEach(candidate ⇒ if (candidate.roleDepth() <= rd) {
          println("candidate: " + candidate + " from thread " + Thread.currentThread().toString())
          val closure2 = clop2(candidate).reduce()
          println("  with closure2: " + closure2)
          if (!closure2.isBot()) {
            if (candidate.isEquivalentTo(closure2)) {
              var closure1 = clop(candidate).reduce()
              println("  with closure1: " + closure1)
              var ask = !candidate.isEquivalentTo(closure1)
              var ignore = false
              var unsatisfiablePremise = false
              while (ask) {
                ask = false
                val future = askExpert(new ELConceptInclusion(candidate, closure1))
                val answer = future.get()
                answer match {
                  case AcceptAnswer()               ⇒ {}
                  case IgnoreAnswer()               ⇒ { ignore = true }
                  case UnsatisfiablePremiseAnswer() ⇒ { unsatisfiablePremise = true }
                  case DeclineAnswer(counterexample) ⇒ {
                    val c = new ELConceptDescription(counterexample)
                    insertCounterexample(c)
                    counterexamples.put(c, getOWLDataFactory().getOWLNamedIndividual(IRI.create(activeOntologyIRI + "#counterexample-" + nextCounterexampleNumber.getAndIncrement())))
                    updateProvidedCounterexamples()
                    closure1 = clop(candidate).reduce()
                    ask = !candidate.isEquivalentTo(closure1)
                  }
                }
              }
              if (!ignore) {
                if (unsatisfiablePremise) {
                  repairedTBox.add(new ELConceptInclusion(candidate, ELConceptDescription.bot()))
                  updateConfirmedAxioms()
                } else {
                  closure1 = clop(candidate).reduce()
                  if (!candidate.isEquivalentTo(closure1)) {
                    repairedTBox.add(new ELConceptInclusion(candidate, closure1))
                    updateConfirmedAxioms()
                  }
                  closure1.lowerNeighborsB(signature).forEach(lowerNeighbor ⇒
                    candidates.add(lowerNeighbor.reduce()))
                }
              }
            } else {
              candidates.add(closure2)
            }
          }
          //        })))
        })
        //        futures.forEach(_.get)
        rank += 1
      }
      println("Repair finished.")
      setStatus("Repair finished.")
      //      pool.shutdown()

      println("Writing changes to ontology...")
      Util.runOnProtegeThread(() ⇒ { getOWLModelManager().getOWLOntologyManager().removeAxioms(getOWLModelManager().getActiveOntology, _refutableTBox) }, true)
      println("Removed old concept inclusions.")
      val _repairedTBox = Sets.newHashSet[OWLAxiom]
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
      println("Cleaning up...")
      counterexamples.clear()
      repairedTBox.clear()
      questions.clear()
      answers.clear()
      updateProvidedCounterexamples()
      updateConfirmedAxioms()
      clearPendingAxioms()
      println("Everything done.")
      Util.runOnProtegeThread(() ⇒ { repairButton.setEnabled(true) }, true)
    }).start()
  }

  private val questions = Sets.newConcurrentHashSet[OWLAxiom]()
  private val answers = new ConcurrentHashMap[OWLAxiom, Answer]

  private var repairButton: Button = _
  private var statusLabel: Label = _

  private def setStatus = statusLabel.setText(_)

  private var counterexampleAxiomListFrame: AxiomListFrame = _
  private var counterexampleAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _

  private var confirmedAxiomListFrame: AxiomListFrame = _
  private var confirmedAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _

  private var pendingAxiomListFrame: AxiomListFrame = _
  private var pendingAxiomList: OWLFrameList[java.util.Set[OWLAxiom]] = _

  private def updateProvidedCounterexamples() {
    val providedCounterexamples = Sets.newHashSet[OWLAxiom]
    counterexamples.entrySet().forEach(counterexample ⇒
      providedCounterexamples.add(getOWLDataFactory().getOWLClassAssertionAxiom(counterexample.getKey().toOWLClassExpression(), counterexample.getValue())))
    counterexampleAxiomList.setRootObject(providedCounterexamples)
    counterexampleAxiomList.refreshComponent()
    counterexampleAxiomList.repaint()
    counterexampleAxiomList.validate()
  }

  private def updateConfirmedAxioms() {
    val confirmedAxioms = Sets.newHashSet[OWLAxiom]
    repairedTBox.forEach(conceptInclusion ⇒
      confirmedAxioms.add(conceptInclusion.toOWLSubClassOfAxiom()))
    confirmedAxiomList.setRootObject(confirmedAxioms)
    confirmedAxiomList.refreshComponent()
    confirmedAxiomList.repaint()
    confirmedAxiomList.validate()
  }

  private def clearPendingAxioms() {
    pendingAxiomList.setRootObject(Collections.emptySet())
    pendingAxiomList.refreshComponent()
    pendingAxiomList.repaint()
    pendingAxiomList.validate()
  }

  private def askExpert(_question: ELConceptInclusion): Future[Answer] = {
    val question = _question.toOWLSubClassOfAxiom()
    println("new question: " + question)
    questions.add(question)
    pendingAxiomList.setRootObject(questions)
    pendingAxiomList.refreshComponent()
    pendingAxiomList.repaint()
    pendingAxiomList.validate()
    new Future[Answer]() {

      override def cancel(mayInterruptIfRunning: Boolean): Boolean = throw new RuntimeException("Not supported")
      override def isCancelled(): Boolean = false
      override def isDone(): Boolean = answers.containsKey(question)

      @throws(classOf[InterruptedException])
      @throws(classOf[ExecutionException])
      override def get(): Answer = {
        while (!isDone())
          Thread.sleep(100)
        answers.get(question)
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
        answers.get(question)
      }
    }
  }

  private abstract class Answer {}
  private case class AcceptAnswer() extends Answer {}
  private case class IgnoreAnswer() extends Answer {}
  private case class UnsatisfiablePremiseAnswer() extends Answer {}
  private case class DeclineAnswer(val counterexample: OWLClassExpression) extends Answer {}

}
