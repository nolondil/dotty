package test

import scala.annotation.Idempotent

object CommonSubexpression {

  @Idempotent def sum(i1: Int, i2: Int) = i1 + i2
  @Idempotent def sum2[A: Numeric](i1: A, i2: A) = implicitly[Numeric[A]].plus(i1, i2)

  def method1: Int = {
    val a = 1
    val c = sum(sum(1, a), 3)
    val d = sum(sum(1, a), 4)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method2: Int = {
    val a = 1
    val c = sum(sum(sum(1, a), 2), 3)
    val d = sum(sum(sum(1, a), 2), 4)
    assert(c == 7)
    assert(d == 8)
    d - c
  }

  def method3: Int = {
    val a = 1
    val c = sum(sum(sum(1, a), 2), 1)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method4: Int = {
    val a = 1
    val b = sum(1, a)
    val c = sum(sum(sum(1, a), 2), 1)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(b == 2)
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method5: Int = {
    val a = 1
    val b = sum(1, a)
    val c = sum(sum(1, a), 2)
    val d = sum(sum(sum(1, a), 2), 2)
    assert(b == 2)
    assert(c == 4)
    assert(d == 6)
    d - c
  }

  def method6: Int = {
    val a = 1
    val c = 3 + sum(1, a)
    val d = sum(1, a) + 4
    assert(c == 5)
    assert(d == 6)
    d - c
  }

  def method7: Int = {
    val a = (1,1)
    val c = 3 + a._1
    val d = a._1 + 3
    assert(c == 4)
    assert(d == 4)
    d - c
  }

  def method8: Boolean = {
    // SHOULD DO NOTHING
    for (x <- List(1, 2, 3); y = x * x; z = x * y; u <- 0 to y) yield x * y * z * u
    true
  }

  def method9: Int = {
    val a = 1
    val c = 3 + sum2(a, a)
    val d = sum2(a, a) + 3
    assert(c == 5)
    assert(d == 5)
    d - c
  }

  def main(args: Array[String]): Unit = {
    println("executing")
    assert(method1 == 1)
    assert(method2 == 1)
    assert(method3 == 1)
    assert(method4 == 1)
    assert(method5 == 2)
    assert(method6 == 1)
    assert(method7 == 0)
    assert(method8 == true)
    assert(method9 == 0)
  }

}
