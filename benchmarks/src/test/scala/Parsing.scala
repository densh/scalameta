package scala.meta
package tools

import scala.{meta => api}

import org.scalameter.api._

object ParsingBenchmark extends PerformanceTest.Microbenchmark {
  var files = List.empty[java.io.File]

  locally {
    def loop(dir: java.io.File): Unit = {
      dir.listFiles.filter(_.isFile).filter(_.getName.endsWith(".scala")).map(file => files = file +: files)
      dir.listFiles.filter(_.isDirectory).map(loop)
    }
    loop(new java.io.File("/Users/Denys/.src/scala/src/library"))
    //loop(new java.io.File("/Users/Denys/.src/scala/src/reflect"))
    //loop(new java.io.File("/Users/Denys/.src/scala/src/compiler"))
  }

  val contents = files.map(file => (file, scala.io.Source.fromFile(file).mkString)).toMap
  val filesGen = Gen.enumeration("files")(files: _*)

  measure method "a" in {
    using(filesGen) in { file =>
      import scala.meta.dialects.Scala211
      contents(file).parse[Source]
    }
  }

  val compilerCommand = new scala.tools.nsc.CompilerCommand(Nil, _ => ???)
  val compilerReporter = new scala.tools.nsc.reporters.StoreReporter
  val global = new scala.tools.nsc.Global(compilerCommand.settings, compilerReporter)
  val run = new global.Run

  measure method "b" in {
    using(filesGen) tearDown { _ =>
      compilerReporter.reset()
    } in { file =>
      global.newUnitParser(contents(file), "<adhoc>").parse
    }
  }
}
