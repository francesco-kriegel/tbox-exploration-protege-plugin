package de.tudresden.inf.lat.tboxexploration

import org.semanticweb.owlapi.model.OWLClassExpression

abstract class Answer {}
case class AcceptAnswer() extends Answer {}
case class IgnoreAnswer() extends Answer {}
case class UnsatisfiablePremiseAnswer() extends Answer {}
case class DeclineAnswer(val counterexample: OWLClassExpression) extends Answer {}
case class InheritedDeclineAnswer() extends Answer {}
case class DeclineAnswerWithoutCounterexample() extends Answer {}