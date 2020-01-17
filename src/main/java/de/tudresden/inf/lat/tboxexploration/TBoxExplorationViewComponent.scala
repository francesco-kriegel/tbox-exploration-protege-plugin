package de.tudresden.inf.lat.tboxexploration

import java.awt.BorderLayout
import java.awt.Button
import java.awt.Color
import java.awt.Dimension
import java.awt.GridBagConstraints
import java.awt.GridBagLayout
import java.awt.GridLayout
import java.awt.Insets
import java.awt.Label
import java.awt.event.ActionListener
import java.awt.event.ComponentEvent
import java.awt.event.ComponentListener
import java.text.ParseException
import java.util.Collections
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ExecutionException
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

import org.protege.editor.core.ProtegeApplication
import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.core.ui.progress.BackgroundTask
import org.protege.editor.core.ui.util.InputVerificationStatusChangedListener
import org.protege.editor.owl.ui.editor.OWLClassExpressionExpressionEditor
import org.protege.editor.owl.ui.editor.OWLGeneralAxiomEditor
import org.protege.editor.owl.ui.frame.OWLFrameSectionRow
import org.protege.editor.owl.ui.view.AbstractOWLViewComponent
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLClassAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom
import org.semanticweb.owlapi.model.parameters.Imports

import Util._
import conexp.fx.core.dl.ELConceptDescription
import javax.swing.JButton
import javax.swing.JCheckBox
import javax.swing.JLabel
import javax.swing.JOptionPane
import javax.swing.JPanel
import javax.swing.JScrollPane
import javax.swing.JSpinner
import javax.swing.ScrollPaneConstants
import javax.swing.SpinnerNumberModel
import javax.swing.UIManager
import javax.swing.SwingWorker
import javax.xml.transform.Result

class TBoxExplorationViewComponent extends AbstractOWLViewComponent {

  private var thread: Thread = _
  private val answers = new ConcurrentHashMap[(OWLAxiom, Integer), Answer]
  //  private val answers = new ConcurrentHashMap[OWLAxiom, Answer]
  //  private val futures = new ConcurrentHashMap[(OWLAxiom, Integer), Future[Answer]]

  private var repairButton: Button = _
  private val repairButtonActionListener_Start: ActionListener = _ ⇒ startRepairThread()
  private val repairButtonActionListener_Stop: ActionListener = _ ⇒ stopRepairThread()
  private var statusLabel: Label = _
  private var staticAxiomList: OWLAxiomList = _
  private var refutableAxiomList: OWLAxiomList = _
  private var counterexampleAxiomList: OWLAxiomList = _
  private var confirmedAxiomList: OWLAxiomList = _
  private var pendingAxiomList: OWLAxiomList = _
  private var pendingAxiomMetadata: java.util.Map[OWLAxiom, Integer] = _

  private var repairIsCancelled = false

  private var exploration: TBoxExploration2 = _

  protected def initialiseOWLView() {
    println("Initializing TBox Exploration View Component...")
    staticAxiomList = new OWLAxiomList("Static Axioms", getOWLEditorKit())
    refutableAxiomList = new OWLAxiomList("Refutable Axioms", getOWLEditorKit())
    counterexampleAxiomList = new OWLAxiomList("Provided Counterexamples", getOWLEditorKit())
    confirmedAxiomList = new OWLAxiomList("Confirmed Axioms", getOWLEditorKit())
    pendingAxiomMetadata = new ConcurrentHashMap[OWLAxiom, Integer]
    pendingAxiomList = new OWLAxiomList("Pending Axioms", getOWLEditorKit()) {
      override protected def getButtons(value: Object): java.util.List[MListButton] = {
        if (value.isInstanceOf[OWLFrameSectionRow[_, _, _]]) {
          val buttons = new java.util.ArrayList[MListButton]
          val frameRow: OWLFrameSectionRow[_, OWLAxiom, _] = value.asInstanceOf[OWLFrameSectionRow[_, OWLAxiom, _]];
          val question = frameRow.getAxiom()
          val counter = pendingAxiomMetadata.get(question)
          question match {
            case subClassOfAxiom: OWLSubClassOfAxiom ⇒ {
              if (!exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom))
                buttons.add(
                  new TextMListButton(
                    "Accept",
                    Color.GREEN.darker(),
                    "\u2713",
                    14,
                    _ ⇒ {
                      if (exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom))
                        showWarning("The repaired ontology becomes inconsistent if this axiom is added.")
                      else {
                        answers.put((subClassOfAxiom, counter), new AcceptAnswer())
                        synchronouslyOnProtegeThread {
                          pendingAxiomList.remove(question)
                          pendingAxiomMetadata.remove(question)
                        }
                      }
                    }))
              if (!exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom))
                buttons.add(
                  new TextMListButton(
                    "Ignore (accept but do not add it to the final result; use this option if the premise cannot be satisfied in the domain of interest, i.e., no counterexample can exist)",
                    Color.GRAY.darker(),
                    "?",
                    14,
                    _ ⇒ {
                      if (exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom))
                        showWarning("The repaired ontology becomes inconsistent if this axiom is added.")
                      else {
                        answers.put((subClassOfAxiom, counter), new IgnoreAnswer())
                        synchronouslyOnProtegeThread {
                          pendingAxiomList.remove(question)
                          pendingAxiomMetadata.remove(question)
                        }
                      }
                    }))
              if (!exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom.getSubClass() SubClassOf Nothing))
                buttons.add(
                  new TextMListButton(
                    "Unsatisfiable Premise (experimental feature)",
                    Color.BLUE.darker(),
                    "\u22A5",
                    15,
                    _ ⇒ {
                      if (exploration.repairedOntologyBecomesInconsistent(subClassOfAxiom.getSubClass() SubClassOf Nothing))
                        showWarning("The repaired ontology becomes inconsistent if this premise is declared as unsatisfiable.")
                      else {
                        answers.put((subClassOfAxiom, counter), new UnsatisfiablePremiseAnswer())
                        synchronouslyOnProtegeThread {
                          pendingAxiomList.remove(question)
                          pendingAxiomMetadata.remove(question)
                        }
                      }
                    }))
              buttons.add(
                new TextMListButton(
                  "Decline",
                  Color.RED.darker(),
                  "\u2715",
                  15,
                  _ ⇒ {
                    askForCounterexample(subClassOfAxiom)
                  }))
            }
            case subPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
              buttons.add(
                new TextMListButton(
                  "Accept",
                  Color.GREEN.darker(),
                  "\u2713",
                  14,
                  _ ⇒ {
                    answers.put((subPropertyChainOfAxiom, counter), new AcceptAnswer())
                    synchronouslyOnProtegeThread {
                      pendingAxiomList.remove(question)
                      pendingAxiomMetadata.remove(question)
                    }
                  }))
              buttons.add(
                new TextMListButton(
                  "Decline",
                  Color.RED.darker(),
                  "\u2715",
                  15,
                  _ ⇒ {
                    answers.put((subPropertyChainOfAxiom, counter), new DeclineAnswerWithoutCounterexample())
                    synchronouslyOnProtegeThread {
                      pendingAxiomList.remove(question)
                      pendingAxiomMetadata.remove(question)
                    }
                  }))
            }
          }
          buttons
        } else
          Collections.emptyList()
      }
    }

    setLayout(new BorderLayout())
    repairButton = new Button("Repair...")
    repairButton.addActionListener(repairButtonActionListener_Start)
    val hideCheckBox = new JCheckBox("Hide static and refutable axioms", false)
    val topPanel = new JPanel()
    topPanel.setLayout(new BorderLayout())
    topPanel.add(hideCheckBox, BorderLayout.WEST)
    topPanel.add(repairButton, BorderLayout.EAST)
    add(topPanel, BorderLayout.NORTH)
    val listPanel = new JPanel()
    listPanel.setLayout(new GridLayout(3, 1))
    val inputPanel = new JPanel()
    inputPanel.setLayout(new GridLayout(1, 2))
    inputPanel.add(new JScrollPane(staticAxiomList))
    inputPanel.add(new JScrollPane(refutableAxiomList))
    listPanel.add(inputPanel)
    hideCheckBox.addActionListener(_ ⇒ {
      //      inputPanel.setVisible(!inputPanel.isVisible())
      if (hideCheckBox.isSelected()) {
        listPanel.remove(inputPanel)
        listPanel.setLayout(new GridLayout(2, 1))
      } else {
        listPanel.add(inputPanel, 0)
        listPanel.setLayout(new GridLayout(3, 1))
      }
      listPanel.validate()
      listPanel.repaint()

    })
    listPanel.add(new JScrollPane(counterexampleAxiomList))
    val outputPanel = new JPanel()
    outputPanel.setLayout(new GridLayout(1, 2))
    outputPanel.add(new JScrollPane(confirmedAxiomList))
    outputPanel.add(new JScrollPane(pendingAxiomList))
    listPanel.add(outputPanel)
    add(listPanel, BorderLayout.CENTER)
    val bottomPanel = new JPanel()
    bottomPanel.setLayout(new BorderLayout())
    statusLabel = new Label()
    bottomPanel.add(statusLabel, BorderLayout.CENTER)
    add(bottomPanel, BorderLayout.SOUTH)
    println("TBox Exploration View Component successfully initialized.")
  }

  protected def disposeOWLView() {
    answers.clear()
    //    futures.clear()
    pendingAxiomMetadata.clear()
    staticAxiomList.dispose()
    refutableAxiomList.dispose()
    counterexampleAxiomList.dispose()
    confirmedAxiomList.dispose()
    pendingAxiomList.dispose()
  }

  var task: BackgroundTask = _

  private def startRepairThread() {
    repairIsCancelled = false
    task = new BackgroundTask() {
      override def toString(): String = {
        "Repairing Ontology using TBox Exploration...\r\n" +
          "┣━ " + getOWLModelManager().getActiveOntology().getOntologyID() + "\r\n" +
          "┗━ Current status: " + statusLabel.getText()
      }
    }
    ProtegeApplication.getBackgroundTaskManager().startTask(task)
    thread = new Thread(() ⇒ repair())
    thread.start()
  }

  private def stopRepairThread() {
    repairIsCancelled = true
    if (thread != null) { // Implement a more elegant way to stop the repairing process
      System.err.println("The following java.lang.ThreadDeath error can be ignored, since it is caused by intentionally stopping a thread.")
      thread.stop()
      cleanup()
      println("Repair cancelled.")
      setStatusLabelText("Repair cancelled.")
    }
  }

  private def repair() {
    synchronouslyOnProtegeThread {
      println("Starting repair...")
      setStatusLabelText("Starting repair...")
      repairButton.removeActionListener(repairButtonActionListener_Start)
      repairButton.setLabel("Stop Repair")
      repairButton.addActionListener(repairButtonActionListener_Stop)
    }

    clearVariables()

    val ontology = getOWLModelManager().getActiveOntology()
    val (allCIs, _) = transformTBox(ontology.getTBoxAxioms(Imports.EXCLUDED))

    //    val inputPremiseRoleDepth =
    //      allCIs.parallelStream().map[Int](_.getSubsumee.roleDepth).max(java.lang.Integer.compare).orElse(0)
    //    val inputConclusionRoleDepth =
    //      allCIs.parallelStream().map[Int](_.getSubsumer.roleDepth).max(java.lang.Integer.compare).orElse(0)
    //    val inputPremiseRank =
    //      allCIs.parallelStream().map[Long](_.getSubsumee.rank5).max(java.lang.Long.compare).orElse(0)
    //    val inputConclusionRank =
    //      allCIs.parallelStream().map[Long](_.getSubsumer.rank5).max(java.lang.Long.compare).orElse(0)

    def specifyArguments(): (Object, Integer, Integer, Boolean, OWLAxiom) = {
      println("asking for arguments...")
      val roleDepthSpinner = new JSpinner(new SpinnerNumberModel(5, 0, 32, 1))
      //      val roleDepthSpinnerStatusLabel = new JLabel(" ")
      //      val maxRankCheckBox = new JCheckBox("maximal rank (deprecated)", true)
      //      val maxRankSpinner = new JSpinner(new SpinnerNumberModel(16, 0, Integer.MAX_VALUE, 1))
      val exploreRoleIncompatibilityAxiomsCheckBox = new JCheckBox(
        "<html>The ontology is not complete for role incompatibility axioms.  If selected, then you will be asked whether<br>" +
          "some binary role compositions are unsatisfiable.  Note that this is an experimental feature.", true)
      val unwantedConsequenceCheckBox = new JCheckBox("unwanted consequence", false)
      val unwantedConsequenceAxiomEditor = new OWLGeneralAxiomEditor(getOWLEditorKit())
      val unwantedConsequenceAxiomEditorComponent = unwantedConsequenceAxiomEditor.getEditorComponent().getComponent(0)
      val unwantedConsequenceStatusLabel = new JLabel(" ")
      val panel = new JPanel()
      panel.setLayout(new GridBagLayout())
      panel.add(
        new JLabel("Please specify the following."),
        new GridBagConstraints(
          0, 0, // gridx, gridy
          2, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.CENTER, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      panel.add(
        new JLabel("maximal role depth"),
        new GridBagConstraints(
          0, 1, // gridx, gridy
          1, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.LINE_END, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      panel.add(
        roleDepthSpinner,
        new GridBagConstraints(
          1, 1, // gridx, gridy
          1, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.LINE_START, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      //      panel.add(
      //        roleDepthSpinnerStatusLabel,
      //        new GridBagConstraints(
      //          1, 2, // gridx, gridy
      //          1, 1, // gridwidth, gridheight
      //          0, 0, // weightx, weighty
      //          GridBagConstraints.LINE_START, // anchor
      //          GridBagConstraints.HORIZONTAL, // fill
      //          new Insets(0, 0, 0, 0), // insets
      //          4, 4 // ipadx, ipady
      //        ))
      //      panel.add(
      //        maxRankCheckBox,
      //        new GridBagConstraints(
      //          0, 3, // gridx, gridy
      //          1, 1, // gridwidth, gridheight
      //          0, 0, // weightx, weighty
      //          GridBagConstraints.LINE_END, // anchor
      //          GridBagConstraints.HORIZONTAL, // fill
      //          new Insets(0, 0, 0, 0), // insets
      //          4, 4 // ipadx, ipady
      //        ))
      //      panel.add(
      //        maxRankSpinner,
      //        new GridBagConstraints(
      //          1, 3, // gridx, gridy
      //          1, 1, // gridwidth, gridheight
      //          0, 0, // weightx, weighty
      //          GridBagConstraints.LINE_START, // anchor
      //          GridBagConstraints.HORIZONTAL, // fill
      //          new Insets(0, 0, 0, 0), // insets
      //          4, 4 // ipadx, ipady
      //        ))
      panel.add(
        exploreRoleIncompatibilityAxiomsCheckBox,
        new GridBagConstraints(
          0, 2, // gridx, gridy
          2, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.CENTER, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      panel.add(
        unwantedConsequenceCheckBox,
        new GridBagConstraints(
          0, 3, // gridx, gridy
          1, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.FIRST_LINE_START, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      panel.add(
        new JScrollPane(
          unwantedConsequenceAxiomEditorComponent,
          ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
          ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED),
        new GridBagConstraints(
          1, 3, // gridx, gridy
          1, 1, // gridwidth, gridheight
          1, 1, // weightx, weighty
          GridBagConstraints.CENTER, // anchor
          GridBagConstraints.BOTH, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      panel.add(
        unwantedConsequenceStatusLabel,
        new GridBagConstraints(
          1, 4, // gridx, gridy
          1, 1, // gridwidth, gridheight
          0, 0, // weightx, weighty
          GridBagConstraints.LINE_START, // anchor
          GridBagConstraints.HORIZONTAL, // fill
          new Insets(0, 0, 0, 0), // insets
          4, 4 // ipadx, ipady
        ))
      val okButton = new JButton("OK")
      val cancelButton = new JButton("Cancel")
      var thread: Thread = new Thread(() ⇒ {})
      //      roleDepthSpinner.addChangeListener(_ ⇒ {
      //        if (roleDepthSpinner.getValue().asInstanceOf[Integer] > 2)
      //          roleDepthSpinnerStatusLabel.setText("Running the algorithm with a role depth greater than 2 might be infeasible.")
      //        else
      //          roleDepthSpinnerStatusLabel.setText(" ")
      //      })
      val statusChangedListener: InputVerificationStatusChangedListener = _ ⇒ {
        System.err.println("The following java.lang.ThreadDeath error can be ignored, since it is caused by intentionally stopping a thread.")
        thread.stop()
        unwantedConsequenceStatusLabel.setText("Please wait...")
        if (unwantedConsequenceAxiomEditor.getEditedObject() != null) {
          val owlClassAxiom: OWLClassAxiom = unwantedConsequenceAxiomEditor.getEditedObject()
          if (owlClassAxiom.isInstanceOf[OWLSubClassOfAxiom]) {
            val owlSubClassOfAxiom = owlClassAxiom.asInstanceOf[OWLSubClassOfAxiom]
            thread = new Thread(() ⇒ {
              println("Starting thread for checking input...")
              val tooDeep = owlSubClassOfAxiom.getSubsumee().roleDepth() > roleDepthSpinner.getValue().asInstanceOf[Integer] ||
                owlSubClassOfAxiom.getSubsumer().roleDepth() > roleDepthSpinner.getValue().asInstanceOf[Integer]
              if (tooDeep) {
                synchronouslyOnProtegeThread {
                  okButton.setEnabled(false)
                  unwantedConsequenceStatusLabel.setText("The class descriptions do not satisfy the role depth bound.")
                }
              } else {
                println("Checking whether input is a tautology...")
                if (isTautology(owlSubClassOfAxiom)) {
                  synchronouslyOnProtegeThread {
                    okButton.setEnabled(false)
                    unwantedConsequenceStatusLabel.setText("This is a tautology and can thus not be removed.")
                  }
                } else {
                  println("Checking whether input is a consequence of the ontology...")
                  if (isEntailed(allCIs, owlSubClassOfAxiom)) {
                    synchronouslyOnProtegeThread {
                      okButton.setEnabled(true)
                      unwantedConsequenceStatusLabel.setText("This is a non-tautological consequence and can be removed.")
                    }
                  } else {
                    synchronouslyOnProtegeThread {
                      okButton.setEnabled(false)
                      unwantedConsequenceStatusLabel.setText("This is not a consequence and can thus not be removed.")
                    }
                  }
                }
              }
            })
            thread.start()
          } else {
            okButton.setEnabled(false)
            unwantedConsequenceStatusLabel.setText("This is not a well-formed subclass-of axiom.")
          }
        } else {
          okButton.setEnabled(false)
          unwantedConsequenceStatusLabel.setText("This is not a well-formed class axiom.")
        }
      }
      unwantedConsequenceAxiomEditor.addStatusChangedListener(statusChangedListener)
      unwantedConsequenceAxiomEditorComponent.setEnabled(false)
      //      maxRankCheckBox.addActionListener(_ ⇒
      //        maxRankSpinner.setEnabled(maxRankCheckBox.isSelected()))
      unwantedConsequenceCheckBox.addActionListener(_ ⇒ {
        unwantedConsequenceAxiomEditorComponent.setEnabled(unwantedConsequenceCheckBox.isSelected())
        if (!unwantedConsequenceCheckBox.isSelected()) {
          unwantedConsequenceStatusLabel.setText(" ")
          okButton.setEnabled(true)
        } else {
          statusChangedListener.verifiedStatusChanged(true)
        }
      })
      val pane = new JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
      okButton.addActionListener(_ ⇒ {
        try {
          roleDepthSpinner.commitEdit()
          //          maxRankSpinner.commitEdit()
          pane.setValue(JOptionPane.OK_OPTION)
        } catch {
          case e: ParseException ⇒ {}
        }
      })
      cancelButton.addActionListener(_ ⇒ {
        pane.setValue(JOptionPane.CANCEL_OPTION)
      })
      val dialog = pane.createDialog("Initial Configuration")
      dialog.setResizable(false)
      dialog.setMinimumSize(new Dimension(150, 300))
      dialog.setVisible(true)
      var axiom: OWLAxiom = unwantedConsequenceAxiomEditor.getEditedObject()
      unwantedConsequenceAxiomEditor.removeStatusChangedListener(statusChangedListener)
      unwantedConsequenceAxiomEditor.dispose()
      (
        pane.getValue(),
        roleDepthSpinner.getValue().asInstanceOf[Integer],
        Integer.MAX_VALUE, // if (maxRankCheckBox.isSelected()) maxRankSpinner.getValue().asInstanceOf[Integer] else Integer.MAX_VALUE,
        exploreRoleIncompatibilityAxiomsCheckBox.isSelected(),
        axiom)

    }

    val (value, roleDepth, maxRank, exploreRoleIncompatibilityAxioms, unwantedConsequence) = specifyArguments()

    //    val roleDepth = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal role depth", 2))
    //    val maxRank = Integer.valueOf(JOptionPane.showInputDialog("Specify the maximal rank", 16))
    //    val exploreRoleIncompatibilityAxioms =
    //      !userAnswersYes(
    //        "<html>Is the ontology complete for role incompatibility axioms?<br>" +
    //          "If you select 'No', then you will be asked whether some binary<br>" +
    //          "role compositions are unsatisfiable.  Note that this is an<br>" +
    //          "experimental feature.")
    //
    //    def askForUnwantedConsequence(): OWLAxiom = {
    //      println("asking for unwanted consequence...")
    //      val axiomEditor = new OWLGeneralAxiomEditor(getOWLEditorKit())
    //      val panel = new JPanel()
    //      panel.setLayout(new GridLayout(0, 1))
    //      panel.add(new JLabel("Please specify the unwanted consequence!"))
    //      panel.add(new JScrollPane(axiomEditor.getEditorComponent()))
    //      val indicator = new Label()
    //      panel.add(indicator)
    //      val okButton = new JButton("OK")
    //      val cancelButton = new JButton("Cancel")
    //      var thread: Thread = new Thread(() ⇒ {})
    //      val statusChangedListener: InputVerificationStatusChangedListener = state ⇒ {
    //        thread.stop()
    //        indicator.setText("Please wait...")
    //        if (axiomEditor.getEditedObject() != null) {
    //          val owlClassAxiom: OWLClassAxiom = axiomEditor.getEditedObject()
    //          if (owlClassAxiom.isInstanceOf[OWLSubClassOfAxiom]) {
    //            val owlSubClassOfAxiom = owlClassAxiom.asInstanceOf[OWLSubClassOfAxiom]
    //            thread = new Thread(() ⇒ {
    //              println("Starting thread for checking input...")
    //              val tooDeep = owlSubClassOfAxiom.getSubsumee().roleDepth() > roleDepth ||
    //                owlSubClassOfAxiom.getSubsumer().roleDepth() > roleDepth
    //              if (tooDeep) {
    //                synchronouslyOnProtegeThread {
    //                  okButton.setEnabled(false)
    //                  indicator.setText("The class descriptions do not satisfy the role depth bound.")
    //                }
    //              } else {
    //                println("Checking whether input is a tautology...")
    //                if (isTautology(owlSubClassOfAxiom)) {
    //                  synchronouslyOnProtegeThread {
    //                    okButton.setEnabled(false)
    //                    indicator.setText("This is a tautology and can thus not be removed.")
    //                  }
    //                } else {
    //                  println("Checking whether input is a consequence of the ontology...")
    //                  if (isEntailed(allCIs, owlSubClassOfAxiom)) {
    //                    synchronouslyOnProtegeThread {
    //                      okButton.setEnabled(true)
    //                      indicator.setText("This is a non-tautological consequence and can be removed.")
    //                    }
    //                  } else {
    //                    synchronouslyOnProtegeThread {
    //                      okButton.setEnabled(false)
    //                      indicator.setText("This is not a consequence and can thus not be removed.")
    //                    }
    //                  }
    //                }
    //              }
    //            })
    //            thread.start()
    //          } else {
    //            okButton.setEnabled(false)
    //            indicator.setText("This is not a well-formed subclass-of axiom.")
    //          }
    //        } else {
    //          okButton.setEnabled(false)
    //          indicator.setText("This is not a well-formed class axiom.")
    //        }
    //      }
    //      axiomEditor.addStatusChangedListener(statusChangedListener)
    //      val pane = new JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
    //      okButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.OK_OPTION))
    //      cancelButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.CANCEL_OPTION))
    //      val dialog = pane.createDialog("Unwanted Consequence")
    //      dialog.setResizable(true)
    //      dialog.setMinimumSize(new Dimension(200, 300))
    //      dialog.setVisible(true)
    //      var axiom: OWLAxiom = null
    //      if (pane.getValue().equals(JOptionPane.OK_OPTION))
    //        axiom = axiomEditor.getEditedObject()
    //      axiomEditor.removeStatusChangedListener(statusChangedListener)
    //      axiomEditor.dispose()
    //      axiom
    //    }
    //    val unwantedConsequence: OWLAxiom = askForUnwantedConsequence()

    if (value.equals(JOptionPane.OK_OPTION)) {
      exploration =
        new TBoxExploration2(
          roleDepth,
          maxRank,
          exploreRoleIncompatibilityAxioms,
          ontology,
          unwantedConsequence,
          getOWLModelManager()) {

          override def handleStaticAxioms(axioms: java.util.Set[OWLAxiom]) {
            synchronouslyOnProtegeThread {
              staticAxiomList set axioms
            }
          }

          override def handleRefutableAxioms(axioms: java.util.Set[OWLAxiom]) {
            synchronouslyOnProtegeThread {
              refutableAxiomList set axioms
            }
          }

          override def handleQuestion(axiom: OWLAxiom, counter: Integer): Future[Answer] = {
            askExpert(axiom, counter)
          }

          override def handleNewCounterexample(axiom: OWLClassAssertionAxiom) {
            synchronouslyOnProtegeThread {
              counterexampleAxiomList add axiom
            }
          }

          override def handleAcceptedAxiom(axiom: OWLAxiom) {
            synchronouslyOnProtegeThread {
              confirmedAxiomList add axiom
            }
          }

          override def setStatus(string: String) {
            synchronouslyOnProtegeThread {
              setStatusLabelText(string)
            }
          }

          override def setProgress(percentage: Integer) {
            // TODO
          }

          override def isCancelled(): Boolean = {
            repairIsCancelled
          }
        }
      exploration.start()
    } else {
      setStatusLabelText("Repair cancelled.")
      println("Repair cancelled.")
    }

    cleanup()
  }

  private def askForCounterexample(subClassOfAxiom: OWLSubClassOfAxiom) {
    //    class WrapJLabel(textWithoutHTML: String) extends JLabel(textWithoutHTML) {
    //      private def updateText() {
    //        println("updating JLabel to width " + getWidth)
    //        setText("<html><p style='width:" + getWidth + "px'>" + textWithoutHTML + "</p></html>")
    //      }
    //      updateText()
    //      addComponentListener(new ComponentListener() {
    //        override def componentResized(e: ComponentEvent) { updateText() }
    //        override def componentMoved(e: ComponentEvent) {}
    //        override def componentShown(e: ComponentEvent) {}
    //        override def componentHidden(e: ComponentEvent) {}
    //      })
    //    }
    val explanationLabel = new JLabel(
      "<html><p style='width:580px'>Please specify a counterexample against " + subClassOfAxiom + "!" +
        " The below editor already contains the most general possible counterexample." +
        " You must modify it such that it describes an existing individual in the domain of interest." +
        " Alternatively, you can use the below button to write the conjunction of the axiom's premise" +
        " and conclusion into the editor and then modify it in a suitable way." +
        " Note that the counterexample must be completely specified up to a depth of " + exploration.roleDepth + "." +
        " Furthermore, implicit counterexamples might be induced.  For instance, if there is a filler" +
        " of an existential restriction at level i and the filler has role depth j, then this filler" +
        " is an implicit counterexample if the difference j minus i is smaller than " + exploration.roleDepth + "," +
        " since it then must be completely specified up to depth " + exploration.roleDepth + " as well.</p></html>")
    val counterexampleEditor = new OWLClassExpressionExpressionEditor()
    counterexampleEditor.setup("", "", getOWLEditorKit())
    counterexampleEditor.initialise()
    counterexampleEditor.setDescription(subClassOfAxiom.getSubClass())
    val counterexampleEditorComponent =
      counterexampleEditor.getComponent().getComponent(0).asInstanceOf[JScrollPane].getComponent(0)
    val setCounterexampleEditorToConclusionButton = new JButton("Write conjunction of premise and conclusion in the counterexample editor for modifying it")
    setCounterexampleEditorToConclusionButton.addActionListener(_ ⇒ {
      counterexampleEditor.setDescription(subClassOfAxiom.getSubClass() and subClassOfAxiom.getSuperClass())
    })
    val indicator = new JLabel()
    val violatedAxiomList = new OWLAxiomList("Violated Axioms", getOWLEditorKit())
    val saturateButton = new JButton("Saturate")
    saturateButton.setEnabled(false)
    saturateButton.addActionListener(_ ⇒ {
      saturateButton.setEnabled(false)
      saturateButton.setText("Computing saturation...")
      val classExpression: ELConceptDescription = counterexampleEditor.getClassExpressions.iterator.next
      new SwingWorker[ELConceptDescription, Nothing]() {
        override def doInBackground(): ELConceptDescription = {
          println("Computing saturation of " + classExpression + "...")
          exploration.saturateCounterexample(classExpression)
        }
        override def done() {
          println("Saturation: " + get)
          counterexampleEditor.setDescription(get)
          saturateButton.setText("Saturate")
        }
      }.execute()
    })
    val panel = new JPanel()
    panel.setLayout(new GridBagLayout())
    panel.add(
      explanationLabel,
      new GridBagConstraints(
        0, 0, // gridx, gridy
        2, 1, // gridwidth, gridheight
        0, 0, // weightx, weighty
        GridBagConstraints.LINE_START, // anchor
        GridBagConstraints.HORIZONTAL, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      setCounterexampleEditorToConclusionButton,
      new GridBagConstraints(
        0, 1, // gridx, gridy
        1, 1, // gridwidth, gridheight
        0, 0, // weightx, weighty
        GridBagConstraints.LINE_START, // anchor
        GridBagConstraints.NONE, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      new JScrollPane(
        counterexampleEditorComponent,
        ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED),
      new GridBagConstraints(
        0, 2, // gridx, gridy
        2, 1, // gridwidth, gridheight
        0, 0.5, // weightx, weighty
        GridBagConstraints.CENTER, // anchor
        GridBagConstraints.BOTH, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      indicator,
      new GridBagConstraints(
        0, 3, // gridx, gridy
        2, 1, // gridwidth, gridheight
        0, 0, // weightx, weighty
        GridBagConstraints.LINE_START, // anchor
        GridBagConstraints.HORIZONTAL, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      new JScrollPane(
        violatedAxiomList,
        ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED),
      new GridBagConstraints(
        0, 4, // gridx, gridy
        2, 1, // gridwidth, gridheight
        0, 1, // weightx, weighty
        GridBagConstraints.CENTER, // anchor
        GridBagConstraints.BOTH, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      saturateButton,
      new GridBagConstraints(
        0, 5, // gridx, gridy
        2, 1, // gridwidth, gridheight
        0, 0, // weightx, weighty
        GridBagConstraints.LINE_START, // anchor
        GridBagConstraints.NONE, // fill
        new Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    val okButton = new JButton("OK")
    val cancelButton = new JButton("Cancel")
    val statusChangedListener: InputVerificationStatusChangedListener = state ⇒ {
      saturateButton.setEnabled(false)
      if (counterexampleEditor.getClassExpressions != null && !counterexampleEditor.getClassExpressions.isEmpty) {
        val classExpression = counterexampleEditor.getClassExpressions.iterator.next
        if (classExpression != null) {
          val isCounterexample = !(classExpression satisfies subClassOfAxiom)
          val violatedConceptInclusions = exploration.getViolatedConceptInclusionsAsOWLAxioms(classExpression)
          violatedAxiomList set violatedConceptInclusions
          okButton.setEnabled(isCounterexample && violatedConceptInclusions.isEmpty)
          indicator.setText(
            "<html><p style='width:580px'>This class expression is " +
              (if (isCounterexample) "" else "not ") +
              "a valid counterexample against the above axiom" +
              (if (violatedConceptInclusions.isEmpty) "."
              else (if (isCounterexample) ", but " else " and ") +
                "it violates the following axioms, which you have already confirmed as valid." +
                " Please adjust the class expression accordingly!  Alternatively, you can" +
                " saturate the entered class expression with respect to these violated axioms" +
                " by clicking the below button.  Note that you must then check whether the resulting" +
                " class expression really describes an individual in the domain of interest.</p></html>"))
          if (!violatedConceptInclusions.isEmpty)
            saturateButton.setEnabled(true)
        } else {
          okButton.setEnabled(false)
          indicator.setText("<html><p style='width:580px'>This is not a well-formed class expression.</p></html>")
        }
      } else {
        okButton.setEnabled(false)
        indicator.setText("<html><p style='width:580px'>This is not a well-formed class expression.</p></html>")
      }
    }
    counterexampleEditor.addStatusChangedListener(statusChangedListener)
    statusChangedListener.verifiedStatusChanged(false)
    val pane = new JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
    okButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.OK_OPTION))
    cancelButton.addActionListener(_ ⇒ pane.setValue(JOptionPane.CANCEL_OPTION))
    val dialog = pane.createDialog("New Counterexample")
    dialog.setResizable(true)
    val size = new Dimension(800, 500)
    //    dialog.setPreferredSize(size)
    dialog.setMinimumSize(size)
    //    dialog.setMaximumSize(size)
    dialog.setSize(size)
    dialog.addComponentListener(new ComponentListener() {
      //      private var lastX: Int = dialog.getLocation.x
      override def componentResized(e: ComponentEvent) {
        dialog.setSize(new Dimension(800, Math.max(400, dialog.getHeight())))
        //        dialog.setLocation(lastX, dialog.getLocation.y)
      }
      override def componentMoved(e: ComponentEvent) {
        //        lastX = dialog.getLocation.x
      }
      override def componentShown(e: ComponentEvent) {
        //        lastX = dialog.getLocation.x
      }
      override def componentHidden(e: ComponentEvent) {}
    })
    dialog.setVisible(true)
    if (pane.getValue().equals(JOptionPane.OK_OPTION)) {
      val counterexample: OWLClassExpression = counterexampleEditor.getClassExpressions().iterator().next()
      answers.put((subClassOfAxiom, pendingAxiomMetadata.get(subClassOfAxiom)), new DeclineAnswer(counterexample))
      synchronouslyOnProtegeThread {
        pendingAxiomList.remove(subClassOfAxiom)
        pendingAxiomMetadata.remove(subClassOfAxiom)
      }
      val counterexamples = Set[ELConceptDescription](counterexample) ++ exploration.getImplicitCompletelySpecifiedCounterexamples(counterexample)
      pendingAxiomList.forEach({
        case otherOWLSubClassOfAxiom: OWLSubClassOfAxiom ⇒ {
          if (!subClassOfAxiom.equals(otherOWLSubClassOfAxiom)) {
            //            if (!(counterexample satisfies otherOWLSubClassOfAxiom)) {
            if (counterexamples exists { c ⇒ !(c satisfies otherOWLSubClassOfAxiom) }) {
              answers.put((otherOWLSubClassOfAxiom, pendingAxiomMetadata.get(otherOWLSubClassOfAxiom)), new InheritedDeclineAnswer())
              synchronouslyOnProtegeThread {
                pendingAxiomList.remove(otherOWLSubClassOfAxiom)
                pendingAxiomMetadata.remove(otherOWLSubClassOfAxiom)
              }
            }
          }
        }
        case owlSubPropertyChainOfAxiom: OWLSubPropertyChainOfAxiom ⇒ {
          if (exploration isACheckedBinaryRoleComposition (
            owlSubPropertyChainOfAxiom.getPropertyChain().get(0).asOWLObjectProperty().getIRI(),
            owlSubPropertyChainOfAxiom.getPropertyChain().get(1).asOWLObjectProperty().getIRI())) {
            answers.put((owlSubPropertyChainOfAxiom, pendingAxiomMetadata.get(owlSubPropertyChainOfAxiom)), new InheritedDeclineAnswer())
            synchronouslyOnProtegeThread {
              pendingAxiomList.remove(owlSubPropertyChainOfAxiom)
              pendingAxiomMetadata.remove(owlSubPropertyChainOfAxiom)
            }
          }
        }
      })
    }
    counterexampleEditor.removeStatusChangedListener(statusChangedListener)
    counterexampleEditor.dispose()
    violatedAxiomList.dispose()
  }

  //  private def askExpert(question: OWLAxiom, counter: Integer): Future[Answer] = synchronized {
  //    println("*** new question: " + question)
  //    synchronouslyOnProtegeThread {
  //      pendingAxiomList add question
  //    }
  //    if (futures containsKey (question, counter))
  //      futures get (question, counter)
  //    else {
  //      val future = new Future[Answer]() {
  //        private var answer: Answer = null
  //        override def cancel(mayInterruptIfRunning: Boolean): Boolean = throw new RuntimeException("Not supported")
  //        override def isCancelled(): Boolean = false
  //        override def isDone(): Boolean = synchronized { answer != null || answers.containsKey(question) }
  //
  //        private def tryGetAnswer() {
  //          synchronized {
  //            if (answer == null) {
  //              answer = answers.get(question)
  //              answers.remove(question)
  //            }
  //          }
  //        }
  //
  //        @throws(classOf[InterruptedException])
  //        @throws(classOf[ExecutionException])
  //        override def get(): Answer = {
  //          while (!isDone()) {
  //            println("Still waiting for an answer for question " + question + " (" + counter + ")...")
  //            Thread.sleep(100)
  //          }
  //          tryGetAnswer()
  //          answer
  //        }
  //
  //        @throws(classOf[InterruptedException])
  //        @throws(classOf[ExecutionException])
  //        @throws(classOf[TimeoutException])
  //        override def get(timeout: Long, unit: TimeUnit): Answer = {
  //          val maxWaitTime = unit.toMillis(timeout)
  //          var curWaitTime = 0
  //          while (!isDone()) {
  //            Thread.sleep(100)
  //            curWaitTime += 100
  //            if (curWaitTime >= maxWaitTime)
  //              throw new TimeoutException
  //          }
  //          tryGetAnswer()
  //          answer
  //        }
  //      }
  //      futures.put((question, counter), future)
  //      future
  //    }
  //  }

  private def askExpert(question: OWLAxiom, counter: Integer): Future[Answer] = {
    println("*** new question: " + question)
    synchronouslyOnProtegeThread {
      pendingAxiomList add question
      pendingAxiomMetadata put (question, counter)
    }
    new Future[Answer]() {
      override def cancel(mayInterruptIfRunning: Boolean): Boolean = throw new RuntimeException("Not supported")
      override def isCancelled(): Boolean = false
      override def isDone(): Boolean = answers containsKey (question, counter)

      @throws(classOf[InterruptedException])
      @throws(classOf[ExecutionException])
      override def get(): Answer = {
        while (!isDone())
          Thread.sleep(100)
        answers get (question, counter)
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
        answers get (question, counter)
      }
    }
  }

  private def setStatusLabelText = statusLabel.setText(_)

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

  private def cleanup() {
    if (task != null)
      ProtegeApplication.getBackgroundTaskManager().endTask(task)
    println("Cleaning up...")
    clearVariables()
    println("Everything done.")
    synchronouslyOnProtegeThread {
      repairButton.setLabel("Repair...")
      repairButton.removeActionListener(repairButtonActionListener_Stop)
      repairButton.addActionListener(repairButtonActionListener_Start)
    }
  }

  private def clearVariables() {
    exploration = null
    answers.clear()
    //    futures.clear()
    pendingAxiomMetadata.clear()
    staticAxiomList.clear()
    refutableAxiomList.clear()
    counterexampleAxiomList.clear()
    confirmedAxiomList.clear()
    pendingAxiomList.clear()
  }

}
