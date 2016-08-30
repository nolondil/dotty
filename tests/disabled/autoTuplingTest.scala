// this test fails in linker,
// as linker rewrites the code before IsInstanceOfEvaluator
// and this leads to discovering that Some isn't a superclass of none :-)
object autoTupling {

  val x = Some(1, 2)

  x match {
    case Some(a, b) => a + b
    case None =>
  }
}
