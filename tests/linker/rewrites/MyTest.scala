import dotty.linker._

@rewrites
object myRules {
  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean)(implicit apure: IsPure[a.type]) =
    Rewrite(from   = x.filter(a).filter(b),
            to     = x.filter(x => a(x) && b(x)))

  def dropAndDropRight(x: List[Int], n: Int, m: Int) =
    Rewrite(from = x.drop(n).dropRight(m),
            to   = x.slice(n, x.size - m))

  def twoDropWhile(x: List[Int], p1: Int => Boolean, p2: Int => Boolean)(implicit apure: IsPure[p1.type]) =
    Rewrite(from = x.dropWhile(p1).dropWhile(p2),
            to   = x.dropWhile(n => p1(n) && p2(n)))

  def genTwoFilters[A](xs: List[A], p1: A => Boolean, p2: A => Boolean)(implicit apure: IsPure[p1.type]) =
    Rewrite(from = xs.filter(p1).filter(p2),
            to   = xs.filter(x => p1(x) && p2(x)))

  // ApplyTree
  /*def filterAndMap(x: List[Int], p: Int => Boolean, f: Int => Int) =
    Rewrite(from = x.filter(p).map(f),
            to   = for (i <- x if p(i)) yield f(i)) */

  // ApplyTree
  /*def twoMaps(x: List[Int], a: Int => Int, b: Int => Int) = 
    Rewrite(
      from = x.map(a).map(b),
      to   = x.map(n => {
        val t = a(n)
        b(t)
      })
    )*/
}

object MyTest {
    def main(args: Array[String]): Unit = {
    List(1,2,3).map(x => 2*x).map(x => x + 1)
    List(1,2,3).filter(_ > 2).filter(_ > 1)
    List(1,2,3).dropWhile(_ < 2).dropWhile(_ < 1)
    List(1,2,3,4,5,6).drop(2).dropRight(2)
  }
}
