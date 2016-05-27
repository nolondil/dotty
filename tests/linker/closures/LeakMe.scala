  class LeakMe[T] { // optimization silently adds cloneable
    def bar(a: Int => Int) = a(2)

    val s = 1
    val payload = List(1, 2, 3)
    def noCapture  =       bar{x => println(x); x}
    def yesCapture =       bar{x => s}
    /* 
     dotty: 
    public int yesCapture() {
        return this.bar((Function1)((JFunction1.mcII.sp)this::$anonfun$yesCapture$1));
    }
   
     linker: 
    public int yesCapture() {
        LeakMe leakMe = (LeakMe)this.clone();
        leakMe.payload$$local = null;
        return this.bar((Function1)((JFunction1.mcII.sp)leakMe::$anonfun$yesCapture$1));
    }
    */
    def getS = s
  }

object Test {
  def main(args: Array[String]): Unit = {
    val l = new LeakMe[Int]
    import l._
//    s
//    getS
    //noCapture; 
    yesCapture
    ()
  }

}

