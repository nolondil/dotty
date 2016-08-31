object Test {
  def eval = {
    var x = 0
    lazy val y = 1/x
    try {
      y
    } catch {
      case _ : Throwable =>
        x = 1
        y
    } 
  }

  def main(args: Array[String]): Unit = {
    assert(eval == 1)
  }
}
