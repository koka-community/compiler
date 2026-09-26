pub type color
  ColorDefault
  ColorRed

// A colored printer has additional coloring and formatting options
pub linear effect coloredPrinter
  fun push-color-settings(s: print-color-settings): ()
  fun pop-color-settings(): ()
  fun update-push-color-settings(f: print-color-settings -> print-color-settings): ()

pub struct print-color-settings
  fcolor: color = ColorDefault

pub fun fcolor(c: color, action)
  update-push-color-settings(fn(old) old(fcolor=c))
  action()
  pop-color-settings()

pub fun main()
  42.println