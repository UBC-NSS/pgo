package pgo.util

import scala.collection.mutable

class NameCleaner {
  private val namesSeen = mutable.HashSet[String]()
  // optimisation: if the same hint is used multiple times, avoid recomputing all previously checked variations
  //               by restarting the search for a clean name at the last clean name's index + 1
  private val hintCounterAcc = mutable.HashMap[String,Int]()

  def addKnownName(name: String): this.type = {
    namesSeen += name
    this
  }

  def cleanName(hint: String): String = {
    if(namesSeen(hint)) {
      var currSuffix = hintCounterAcc.getOrElse(hint, 0)
      var currName = s"$hint$currSuffix"
      while(namesSeen(currName)) {
        currSuffix += 1
        currName = s"$hint$currSuffix"
      }
      namesSeen += currName
      hintCounterAcc(hint) = currSuffix + 1
      currName
    } else {
      namesSeen += hint
      hint
    }
  }
}
