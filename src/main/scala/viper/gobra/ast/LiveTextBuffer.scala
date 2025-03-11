package viper.gobra.ast

import java.net.URI
import java.nio.file.{Files, Paths}
import scala.jdk.CollectionConverters._
import scala.collection.concurrent.TrieMap
import org.eclipse.lsp4j.TextDocumentContentChangeEvent
import scala.collection.mutable

object LiveTextBuffer {

  private var fileBuffers: mutable.Map[String, TrieMap[Int, mutable.TreeMap[Int, Char]]] = mutable.Map()

  private val fileCache: TrieMap[String, String] = TrieMap()
  def updateFile(uri: String, content: String): Unit = {
    fileCache.put(uri, content)
  }

  def getFileContent(uri: String): Option[String] = {
    fileCache.get(uri)
  }

  // Initialize buffer when file is opened
  def initializeBuffer(uri: String, content: String): Unit = {
    fileBuffers(uri) = TrieMap()
  }

  def clearBuffers(): Unit = {
    fileBuffers.clear()
  }


  // Update buffer when a change is detected
  def updateBuffer(uri: String, changes: List[TextDocumentContentChangeEvent]): Unit = {
    val fileBuffer = fileBuffers.getOrElseUpdate(uri, TrieMap())

    changes.foreach { change =>
      val startLine = change.getRange.getStart.getLine
      val startChar = change.getRange.getStart.getCharacter
      val endChar = change.getRange.getEnd.getCharacter
      val text = change.getText

      println(s"🔹 Change detected: startLine=$startLine, startChar=$startChar, endChar=$endChar, text='$text'")

      // Retrieve or initialize the character-level tracking for this line
      val lineBuffer = fileBuffer.getOrElseUpdate(startLine, mutable.TreeMap())

      if (text.nonEmpty) {
        // 🌟 Case: Insert characters at specific positions
        text.zipWithIndex.foreach { case (char, i) =>
          val pos = startChar + i
          lineBuffer(pos) = char
        }
        println(s"✅ Inserted: '$text' at position $startChar")
      } else {
        // 🌟 Case: Delete characters from a range
        val toRemove = lineBuffer.range(startChar, endChar).keys.toList
        toRemove.foreach(lineBuffer.remove)
        println(s"❌ Deleted characters from position $startChar to $endChar")
      }
    }

    println(s"📌 Final Buffer: $fileBuffers")
  }



  // Retrieve a full line at a specific cursor position
  def getLineAtPosition(uri: String, line: Int): Option[String] = {
    fileBuffers.get(uri) match {
      case Some(fileBuffer) =>
        fileBuffer.get(line) match {
          case Some(charMap) =>
            // ✅ Sort characters by position and reconstruct the string
            val reconstructedLine = charMap.toSeq.sortBy(_._1).map(_._2).mkString
            Some(reconstructedLine)

          case None => loadLineFromDisk(uri, line) // Fallback if line is not stored
        }

      case None => loadLineFromDisk(uri, line) // Fallback if file is not in buffer
    }
  }

  private def loadLineFromDisk(uri: String, line: Int): Option[String] = {
    val path = Paths.get(URI.create(uri))
    try {
      val lines = Files.readAllLines(path).asScala
      if (line >= 0 && line < lines.length) Some(lines(line)) else None
    } catch {
      case _: Exception => None
    }
  }
  def reloadFile(uri: String): Unit = {
    fileBuffers.remove(uri)
  }
}

