package de.tudresden.inf.lat.tboxexploration

import java.awt.Graphics2D
import org.protege.editor.core.ui.list.MListButton
import java.awt.event.ActionListener
import java.awt.Color
import java.awt.Font

class TextMListButton(tooltipText: String, rollOverColor: Color, buttonText: String, buttonTextSize: Int, listener: ActionListener)
  extends MListButton(tooltipText: String, rollOverColor: Color, listener: ActionListener) {

  /**
   * The code of this method is copied and slightly modified from the class
   * org.exquisite.protege.ui.buttons.UnicodeButton in the Ontology Debugger Plugin for Protégé
   * @see https://git-ainf.aau.at/interactive-KB-debugging/debugger/blob/4a2e4c8ee36a8f63bf7facd099021420b0621cc9/protege-plugin/src/main/java/org/exquisite/protege/ui/buttons/UnicodeButton.java
   */
  override def paintButtonContent(g: Graphics2D) {
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

  override protected def getSizeMultiple(): Int = { 4 }

}