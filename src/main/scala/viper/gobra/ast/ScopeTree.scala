package viper.gobra.ast

import viper.gobra.ast.frontend._
import org.bitbucket.inkytonik.kiama.relation.Tree
import org.bitbucket.inkytonik.kiama.util._
import org.eclipse.lsp4j.{Position => LocPosition}
import viper.gobra.frontend.info.base.{SymbolTable, Type}
import viper.gobra.frontend.info.TypeInfo
import org.eclipse.lsp4j.CompletionItem
import org.eclipse.lsp4j.CompletionItemKind
import org.eclipse.lsp4j.Range
import org.eclipse.lsp4j.Location
import org.bitbucket.inkytonik.kiama.relation.NodeNotInTreeException
import viper.gobra.ast.ScopeTree.ScopeNode
import viper.gobra.frontend.Parser.ParseResult

import java.nio.file.Paths
import scala.annotation.tailrec
import java.io.{File, InputStream, PrintWriter}
import java.net.URI
import scala.collection.mutable


object ScopeTree {

  //private case class TreeNode[T](var value: T, var children: Vector[TreeNode[T]],var parent: Option[TreeNode[T]])

  private case class TreeNode[T](
                                  var value: T,
                                  var children: Vector[TreeNode[T]],
                                  var parent: Option[TreeNode[T]]
                                ) {
    override def toString: String = {
      val parentInfo = parent.map(_ => "Some(parent)").getOrElse("None") // Avoid infinite recursion
      s"TreeNode(value = $value, children = ${children.length}, parent = $parentInfo)"
    }
  }


  private case class PackageContext(pack: PPackage, root: TreeNode[ScopeNode[PNode]],
                                    sources : Vector[Source], tree: Tree[PNode, PPackage],
                                    importMap: mutable.Map[PNode, String], typeInfo: TypeInfo,
                                    pkgFile: Map[String, TreeNode[ScopeNode[PNode]]])
  private var packageContexts: Map[String, PackageContext] = Map()




  //Helper function to return start of node
  private def nodeStartPosition[T](pack: PPackage, scope: T): Position = {
    pack.positions.positions.getStart(scope) match {
        case Some(x) => x
        case None => Position(-1,-1,null) //throw new IllegalStateException(s"$scope Scope start position not found.")
      }
  }

  //Helper function to return end of node
  private def nodeEndPosition[T](pack: PPackage, scope: T): Position = {
    pack.positions.positions.getFinish(scope) match {
        case Some(x) => x
        case None => Position(-1,-1,null) //throw new IllegalStateException("Scope start position not found.")
      }
  }

  //Helper function to print the direct children of a node
  private def printDirectChildren[T](node: TreeNode[T]): Unit = {
    node.children.foreach(child => println(child.value))
  }

  //Helper function to print the AST tree
  private def printAstTree(pack : PPackage, node: PNode, depth: Int = 0): Unit = {
    val indent = "  " * depth

    println(s"$indent- $node is ${node.getClass.getName}")
    val tree = packageContexts(pack.packageClause.id.name).tree
    val children = tree.child(node)
    children.foreach(child => printAstTree(pack, child, depth + 1))

  }

  //Helper function to print the ScopeTree tree
  private def printTree[T](node: TreeNode[T], indent: String = ""): Unit = {
    println(s"$indent${node.value}") // Print the current node's value
    node.children.foreach(child => printTree(child, indent + "  ")) // Recursively print children with additional indentation
  }

  //Helper function to compare the relative position of two nodes
  private def isAfter(pos1: Position, pos2: Position): Boolean = {
    pos1.line > pos2.line || (pos1.line == pos2.line && pos1.column >= pos2.column)
  }

  //Helper function to get children of a node safely
  private def safeChild(node: PNode, pack: PPackage): Vector[PNode] = {
    val t = packageContexts(pack.packageClause.id.name).tree
    try {
      //          println(s"node identity: ${System.identityHashCode(node)}")
      //          println(s"t.nodes identities: ${t.nodes.map(System.identityHashCode)}")
      t.child(node)
    } catch {
      case _: NodeNotInTreeException[PNode] => println(s"the node was not found in the tree, so empty children was returned")
        Vector.empty[PNode] // Return an empty vector if the node is not in the tree
    }
  }

  private def collectDefsAndVars(node: TreeNode[ScopeNode[PNode]]): Vector[PNode] = {
    // Collect the defs and vars of the current node
    val current = node.value.elements.defs ++ node.value.elements.vars

    // Recursively collect from children
    val fromChildren = node.children.flatMap(collectDefsAndVars)

    // Combine and return
    current ++ fromChildren
  }

  //Function to initialize the ScopeTree
  def initialize(pkgs: Iterable[Option[ParseResult]], typeInfo: TypeInfo): Unit ={

    pkgs.foreach {
      case Some(Right((sources, pkg))) =>
        val tree = new Tree[PNode, PPackage](pkg)
        var importMap = mutable.Map[PNode, String]()
        val imports = pkg.imports.map {
          case qualifiedImport: PExplicitQualifiedImport =>
            qualifiedImport.qualifier.toString
          case a =>
            a.importPath
        }
        var realImports = mutable.Map[String, String]()
        pkg.imports.foreach {
          case i: PExplicitQualifiedImport =>
            realImports += (i.qualifier.toString -> i.importPath)
          case a : PNode =>
            realImports += (a.importPath -> a.importPath)
        }

        val unqualifiedImports = pkg.imports.filter(_.isInstanceOf[PUnqualifiedImport])

        for(dot <- tree.nodes.filter(_.isInstanceOf[PDot]).map(_.asInstanceOf[PDot])){
          if(imports.contains(dot.base.toString)){
            importMap += (dot.id -> realImports(dot.base.toString))
          }
        }
        val pkgId = pkg.packageClause.id.name
        val typeTree = if(typeInfo.pkgInfo.name == pkgId){
          typeInfo
        }else{
          null
        }

        packageContexts += (pkgId -> PackageContext(pkg, null, sources, tree, importMap, typeTree, null))
        var pkgFile = Map[String, TreeNode[ScopeNode[PNode]]]()
        for(program <- pkg.programs){
          val rootNode = makeChildren(pkg, program, None)
          pkgFile += (nodeStartPosition(pkg, program).source.name -> rootNode)
        }

        val elems: ScopeElements = ScopeElements(
          pkgFile.flatMap(_._2.value.elements.defs).toVector,
          pkgFile.flatMap(_._2.value.elements.vars).toVector,
          pkgFile.map(_._2.value.elements.referenceMap).flatten.toMap
        )
        val node: ScopeNode[PNode] = ScopeNode(
          nodeStartPosition(pkg, pkg).line,
          nodeEndPosition(pkg, pkg).line,
          elems,
          None
        )
        val rootNode = TreeNode(node, pkgFile.values.toVector, None)
        for(p <- pkgFile){
          p._2.parent = Some(rootNode)
        }
        packageContexts = packageContexts.updated(pkgId, packageContexts(pkgId).copy(root = rootNode, pkgFile = pkgFile))
//        if(pkgId == "pkg"){
//          val node = collectDefsAndVars(rootNode)
//          node.foreach { a =>
//            try {
//              println(s"type $a is ${typeInfo.typ(a.asInstanceOf[PIdnNode])}")
//            } catch {
//              case e: Exception =>
//                println(s"type $a Exception occurred")
//            }
//          }
//
//        }
      case None => println("Invalid or missing package.")
    }
    packageContexts.values.foreach{
      a =>
        val unqualifiedImports = a.pack.imports.filter(_.isInstanceOf[PUnqualifiedImport])
        val funcToImportPath: Map[PNode, String] = unqualifiedImports.flatMap { imp =>
          val decs = resolvePMember(packageContexts(imp.importPath).pack.declarations)
          decs.map {  f => f -> imp.importPath }
        }.toMap
        a.importMap ++= funcToImportPath
        val funcs: Vector[PNode] = unqualifiedImports.flatMap { imp =>
          resolvePMember(packageContexts(imp.importPath).pack.declarations)
        }
        a.root.value = a.root.value.copy(
          elements = a.root.value.elements.copy(
            vars = a.root.value.elements.vars ++ funcs,
            defs = a.root.value.elements.defs ++ funcs
          )
        )
    }
    packageContexts.foreach {
      a =>
        if(a._2.pack.packageClause.id.name == "time"){

        }else {
          println(s"the package ${a._2.pack.packageClause.id.name} has tree:")
          printTree(a._2.root)
        }
    }
  }
  def getSymbolRange(symbol: PNode, uri: String): Range = {
    val pkg = findPkgFromSrc(uri)
    val startPos = nodeStartPosition(pkg, symbol)
    val endPos = nodeEndPosition(pkg, symbol)

    new Range(
      new LocPosition(startPos.line - 1, startPos.column - 1),
      new LocPosition(endPos.line - 1, endPos.column - 1)
    )
  }
  private def isImportedSymbol(symbol: PNode, pkg: PPackage): Boolean = {
    val context = packageContexts.get(pkg.packageClause.id.name)
    context match {
      case Some(ctx) =>
        ctx.importMap.exists { case (node, importPath) => node.toString == symbol.toString }
      case None => false
    }
  }

  private def isFromDifferentFile(symbol: PNode, currentUri: String): Boolean = {
    val pkg = findPkgFromSrc(currentUri)
    val symbolPos = nodeStartPosition(pkg, symbol)
    val defNode = findDef(pkg, symbol, symbolPos.line, symbolPos.column)
    // Extract file path from symbol's source
    val symbolFile = symbolPos.source
    val defNodeFile = nodeStartPosition(pkg, defNode).source

    symbolFile != defNodeFile // If they are different, return true
  }

  private def isBuiltinOrConst(symbol: PNode): Boolean = {
    val builtinKeywords = Set(
      "break", "default", "func", "interface", "select", "case", "defer", "go", "map", "struct",
      "chan", "else", "goto", "package", "switch", "const", "fallthrough", "if", "range", "type",
      "continue", "for", "import", "return", "var"
    )

    // Check if it's a keyword
    if (builtinKeywords.contains(symbol.toString)) {
      return true
    }

    // Check if it's a constant declaration
    symbol match {
      case c : PIdnNode => false
      case _ => true
    }
  }

  def canRenameSymbol(uri: String, position: LocPosition): Either[String, PNode] = {
    val pkg = findPkgFromSrc(uri)
    val symbolOpt = findSymbolAtPosition(uri, position)

    symbolOpt match {
      case Some(symbol) =>
        if (isImportedSymbol(symbol, pkg))
          return Left("Renaming imported symbols is not allowed.")

        if (isBuiltinOrConst(symbol))
          return Left("This symbol is read-only and cannot be renamed.")

        if (isFromDifferentFile(symbol, uri))
          return Left("Renaming variables from another file is not allowed.")

        // ✅ If it passes all checks, return the symbol
        Right(symbol)

      case None => Left("No symbol found at this position.")
    }
  }


  private def findPkgFromSrc(src: String): PPackage = {
    val pkgOpt = packageContexts.values.find { context =>
      context.sources.exists { source =>
        val sourcePath = Paths.get(URI.create(source.name).getPath).normalize().toAbsolutePath.toString
        val queryPath = Paths.get(URI.create(src).getPath).normalize().toAbsolutePath.toString

        sourcePath == queryPath
      }
    }

    pkgOpt match {
      case Some(p) => p.pack
      case None    => throw new IllegalStateException(s"No package found for source: $src (could be a comparison problem)")
    }
  }

  private def getOffset(content: String, position: LocPosition): Int = {
    val lines = content.split("\n")
    val lineIndex = position.getLine
    val columnIndex = position.getCharacter

    if (lineIndex < lines.length) {
      val lineStartOffset = lines.take(lineIndex).map(_.length + 1).sum // Sum up previous lines' lengths
      lineStartOffset + columnIndex
    } else {
      -1 // Invalid position
    }
  }

  private def getFileContent(uri: String): String = {
    LiveTextBuffer.getFileContent(uri).getOrElse {
      val path = Paths.get(new URI(uri))
      new String(java.nio.file.Files.readAllBytes(path)) // Fallback to reading from disk
    }
  }


  private def getWordBeforeDot(uri: String, position: LocPosition): Vector[String] = {
    LiveTextBuffer.getLineAtPosition(uri, position.getLine) match {
      case Some(line) =>
        val beforeCursor = line.take(position.getCharacter)
        println(s"beforeCursor: $beforeCursor")
        val words = beforeCursor.split("\\s+|\\(|\\)|\\{|\\}|\\[|\\]|;|,|\\.")
        println(s"the words: ${words.mkString(", ")}")
        words.toVector
      case None => Vector()
    }
  }

  private def isImport(pkg: PPackage, name: String): Option[PPackage] = {
    packageContexts.get(pkg.packageClause.id.name) match {
      case Some(context) =>
        context.pack.imports.collectFirst {
          case node : PExplicitQualifiedImport if node.qualifier.toString == name => packageContexts.get(node.importPath).map(_.pack)
        }.flatten
      case None => None
    }
  }
  private def resolvePMember(member : Vector[PMember]) : Vector[PNode] = {
    member.flatMap {
      case func: PFunctionDecl => Vector(func.id)
      case f: PFPredicateDecl => Vector(f.id)
      case m: PMPredicateDecl => Vector(m.id)
      case typ: PTypeAlias => Vector(typ.left)
      case typ: PTypeDecl => Vector(typ.left)
      case typ: PTypeDef => Vector(typ.left)
      case method: PMethodDecl => Vector(method.id)
      case vars: PVarDecl => vars.left
      case consts: PConstDecl => consts.specs.flatMap(_.left)
      case _ => Vector()
    }
  }
  private def isStructOrObject(scopeNode: TreeNode[ScopeNode[PNode]], name: String): Option[PTypeDef] = {
    scopeNode.value.elements.defs.collectFirst {
      case struct: PTypeDef if struct.left.name == name => struct
    }
  }
  private def findNodeName(pkg: PPackage, word: String, root : TreeNode[ScopeNode[PNode]]) : PNode = {
    val found = root.value.elements.defs.find(a => a.toString == word)
    found match {
      case Some(d) => return d
      case None =>
        for(c <- root.children){
          val foundChild = findNodeName(pkg, word, c)
          if (foundChild != null) return foundChild
        }
    }
    null
  }
  private def handleDot(uri: String, position: LocPosition, token: Option[String], scope: TreeNode[ScopeNode[PNode]]): List[CompletionItem] = {
    var pkg = findPkgFromSrc(uri)
    val words = getWordBeforeDot(uri, position)
    val beforeDotWord =  words.lastOption match {
      case Some(word) => word
      case None => return List.empty
    }
    println(s"beforeDotWord: $beforeDotWord")
    isImport(pkg, beforeDotWord) match {
      case Some(importedPkg) =>
        // TODO:this had colors fix!
//        return resolvePMember(importedPkg.declarations).collect{
//          a =>
//            val item = new CompletionItem(a.toString)
//            item.setKind(CompletionItemKind.Class)
//            item
//        }.toList
        return importedPkg.declarations.collect {
          case func: PFunctionDecl =>
            val item = new CompletionItem(func.id.toString)
            item.setKind(CompletionItemKind.Function)
            item
          case typeDef: PTypeDef =>
            val item = new CompletionItem(typeDef.left.name)
            item.setKind(CompletionItemKind.Class)
            item
        }.toList
      case None =>
    }
    for(w <- words){
      isImport(pkg, w) match {
        case Some(p) => println(s"pkg switched $w");pkg = p
        case None =>
      }
    }


    val foundNode = findNodeName(pkg, beforeDotWord, packageContexts(pkg.packageClause.id.name).root)

    val typeInfo = packageContexts(pkg.packageClause.id.name).typeInfo
    val typ = try {
      Option(typeInfo)
        .map(_.typ(foundNode.asInstanceOf[PIdnNode]))
        .getOrElse(foundNode)
    } catch {
      case _: Exception => foundNode
    }

    println(s"found type is ${typ.toString}")

    pkg = packageContexts.values.map(_.pack).find{
      p =>
        resolvePMember(p.declarations).map(_.toString).contains(typ.toString)
    }.getOrElse(pkg)

    val typeDef = if(typ.toString == "Type"){
      findNodeName(pkg, beforeDotWord, packageContexts(pkg.packageClause.id.name).root)

    }else {
      findNodeName(pkg, typ.toString, packageContexts(pkg.packageClause.id.name).root)

    }
    val tree = packageContexts(pkg.packageClause.id.name).tree
    //TODO: something here
    typeDef match {
      case n: PNode =>
        tree.parent(n).head match {
          case typeDef : PTypeDef if typeDef.right.isInstanceOf[PStructType] =>
            return getStructFields(typeDef).map { field =>
              val item = new CompletionItem(field.id.toString)
              item.setKind(CompletionItemKind.Field)
              item
            }.toList
          case _ =>
        }
      case null =>
    }
    val structTypeOpt = scope.value.elements.vars.collectFirst {
      case idnDef: PIdnDef if idnDef.name == beforeDotWord =>
        tree.parent(idnDef).head match {
          case typeDef: PTypeDef if typeDef.right.isInstanceOf[PStructType] =>
            println(s"✅ Found struct: ${typeDef.left.name}")
            typeDef
          case _ => None
        }
    }
    structTypeOpt match {
      case Some(structType : PTypeDef) =>
        return getStructFields(structType).map { field =>
          val item = new CompletionItem(field.id.toString)
          item.setKind(CompletionItemKind.Field)
          item
        }.toList
      case None =>
    }
    println(s"nothing works with this dot, what's wrong with you")
    List.empty
  }

  private def getStructFields(struct: PTypeDef): Vector[PFieldDecl] = {
    struct.right match {
      case s: PStructType => s.fields
      case _ => Vector() // If it's not a struct, return an empty vector
    }
  }

  def getCompletions(uri: String, position: LocPosition, token: Option[String]): List[CompletionItem] = {

    val pkg = findPkgFromSrc(uri)
    val pos: Position = Position(position.getLine + 1, position.getCharacter + 1, FileSource(Paths.get(new URI(uri)).toString))

    val file = findFile(pkg, pos)
    val node = findNode(pkg, file, pos)
    val scopeNode = findCompletionScope(pkg, node, packageContexts(pkg.packageClause.id.name).pkgFile(URI.create(uri).getPath), pos.line, pos.column)
    if (scopeNode == null) return List.empty

    val fileContent = getFileContent(uri)
    if(fileContent == "."){
      return handleDot(uri, position, token, scopeNode)
    }

    val allVars = LazyList.iterate(Option(scopeNode))(_.flatMap(_.parent))
      .takeWhile(_.isDefined).flatten.flatMap(_.value.elements.vars).toVector
    val uniqueVars = allVars.groupBy(_.toString).map(_._2.head).toVector


    val completionItems = uniqueVars.map { defNode =>
      val item = new CompletionItem(defNode.toString)

      defNode match {
        case _: PFunctionDecl => item.setKind(CompletionItemKind.Function)
        case _: PMethodDecl => item.setKind(CompletionItemKind.Method)
        case _: PIdnDef => item.setKind(CompletionItemKind.Variable)
        case _: PTypeDef => item.setKind(CompletionItemKind.Class)
        case _ => item.setKind(CompletionItemKind.Text)
      }
      item
    }

    completionItems.toList
  }

  private def findCompletionScope(pkg: PPackage, toFind: PNode, node : TreeNode[ScopeNode[PNode]], line : Int, column: Int) : TreeNode[ScopeNode[PNode]] = {
    val n = node
    val children = node.children
    if(children.isEmpty){
      return n
    }
    for (c <- children){
      if(c.value.scopeStart <= line && line <= c.value.scopeEnd){
        val found = findCompletionScope(pkg, toFind, c, line, column)
        if (found != null) {
          return found // Return as soon as we find a match
        }
      }
    }
    n
  }



  private def findImports(pkg: PPackage, node : PNode) : (PPackage, PNode) = {
    if(packageContexts(pkg.packageClause.id.name).importMap.contains(node)){
      val pkg1 = packageContexts(packageContexts(pkg.packageClause.id.name).importMap(node)).pack
      val decs = packageContexts(pkg1.packageClause.id.name).pack.declarations

      val realDecs = resolvePMember(decs)
      (pkg1, realDecs.find(a => a.toString == node.toString).get)
    }else{
      null
    }

  }

  def distinctBy[T](seq: Seq[T], keyExtractor: T => (Int, Int)): Seq[T] = {
    seq.groupBy(keyExtractor).values.map(_.head).toSeq
  }

  def findReferencesInProject(uri: String, position: LocPosition): Vector[Location] = {
    val symbolOpt = findSymbolAtPosition(uri, position)
    var pkg = findPkgFromSrc(uri)

    val scope: TreeNode[ScopeNode[PNode]] = symbolOpt match {
      case Some(node) => findScope(pkg, node, packageContexts(pkg.packageClause.id.name).pkgFile(URI.create(uri).getPath), position.getLine, position.getCharacter)
      case None => throw new IllegalStateException("no scope found in findReferencesInProject")
    }

    symbolOpt match {
      case Some(symbol) =>

        val references = findRefs(symbol, scope).appended(symbol)
          .distinctBy(ref => (nodeStartPosition(pkg, ref).line, nodeStartPosition(pkg, ref).column))

        val locations = references.map{
          x =>
            if(nodeStartPosition(pkg, x).source != null){
              val range = new Range(
                new LocPosition(nodeStartPosition(pkg, x).line - 1, nodeStartPosition(pkg, x).column - 1),
                new LocPosition(nodeEndPosition(pkg, x).line - 1, nodeEndPosition(pkg, x).column - 1)
              )
              new Location(Paths.get(nodeStartPosition(pkg, x).source.name).toUri.toString, range)
            }else{
              null
            }

        }.filter(_ != null)

        var imp = findImports(pkg, symbol)
        val unjustRefs = references.filter(a => nodeStartPosition(pkg, a).source == null)
        if(unjustRefs.nonEmpty){
          for(ref <- unjustRefs){
            val unq = pkg.imports.filter(_.isInstanceOf[PUnqualifiedImport]).map(_.importPath)
            val realPkg = packageContexts.keys.find(a => unq.contains(a)).get
            pkg = packageContexts(realPkg).pack
            val decs = packageContexts(pkg.packageClause.id.name).pack.declarations
            val realDecs = resolvePMember(decs)
            val t = realDecs.find(a => a.toString == ref.toString).get
            imp = (pkg, t)
          }
        }
        if(imp == null){
          return locations
        }
        val defNode = imp._2
        pkg = imp._1

        defNode match {
          case null => locations
          case x =>
            val path = nodeStartPosition(pkg, x).source.name
            val p = if(path.substring(0,5) == "stubs"){
              writeBuiltInPackageToFile(pkg).toURI.toString
            }else{
              Paths.get(nodeStartPosition(pkg, x).source.name).toUri.toString
            }
            locations.appended(
              new Location(p, new Range(
                new LocPosition(nodeStartPosition(pkg, x).line - 1, nodeStartPosition(pkg, x).column - 1),
                new LocPosition(nodeEndPosition(pkg, x).line - 1, nodeEndPosition(pkg, x).column - 1)
              ))
            )
        }

      case None =>
        println(s"No symbol found at $position in $uri")
        Vector.empty
    }
  }

  private def checkForNodeInDefs(node: PNode, treeNode: TreeNode[ScopeNode[PNode]]) : Option[PNode] = {
    treeNode.value.elements.defs.find(obj => obj != null && node != null && obj.toString == node.toString)
  }

  private def findRefsUp(node: PNode, treeNode: TreeNode[ScopeNode[PNode]]) : Vector[PNode] = {
    val found = checkForNodeInDefs(node, treeNode)
    found match {
      case Some(obj) => treeNode.value.elements.vars.filter(x => x.toString == node.toString) ++ Vector(obj)
      case None =>
        treeNode.parent match {
          case Some(parent) =>
            treeNode.value.elements.vars.filter(x => x.toString == node.toString) ++ findRefs(node, parent)
          case None => Vector()
        }
    }
  }

  private def findRefsDown(node: PNode, treeNode: TreeNode[ScopeNode[PNode]]) : Vector[PNode] = {
    val stop = checkForNodeInDefs(node, treeNode)
    stop match{
      case Some(s) =>
        println(s"object $s redefined, we stop"); return Vector()
      case None =>
    }
//    val found = checkForNodeInVars(node, treeNode)
//    found match {
//      case Some(obj) => treeNode.value.elements.vars.filter(x => x.toString == node.toString) ++ Vector(obj)
//      case None =>
    treeNode.value.elements.vars.filter(x => x.toString == node.toString) ++
      treeNode.children.flatMap(c => findRefsDown(node, c))
//        treeNode.parent match {
//          case Some(parent) =>
//            treeNode.value.elements.vars.filter(x => x.toString == node.toString) ++ findRefs(node, parent)
//          case None => Vector()
//        }
    //}
  }

  private def findRefs(node: PNode, treeNode: TreeNode[ScopeNode[PNode]]) : Vector[PNode] = {
    findRefsUp(node, treeNode) ++ treeNode.children.flatMap(c => findRefsDown(node, c))
  }

  def getSymbolType(uri: String, symbol: PNode): Type.Type = {
    val pkg = findPkgFromSrc(uri)
    val typeInfo = packageContexts(pkg.packageClause.id.name).typeInfo
    symbol match {
      case node: PIdnNode => typeInfo.typ(node)
      case _ => null
    }
  }

  def findSymbolAtPosition(uri: String, position: LocPosition): Option[PNode] = {
    val pkg = findPkgFromSrc(uri)

    val source = FileSource(Paths.get(new URI(uri)).toString)
    val pos = Position(position.getLine + 1, position.getCharacter + 1, source)
    val file = findFile(pkg, pos)

    Some(findNode(pkg, file, pos))
  }

//  private def searchForSymbolInTree(symbol: PNode): Vector[PNode] = {
//    val results = for {
//      (_, context) <- packageContexts
//      tree = context.tree
//      nodes = tree.nodes
//      matches = nodes.filter { node =>
//        symbol.toString == node.toString
//      }
//    } yield matches
//    results.flatten.toVector
//  }

//  private def searchForSymbolInTree(symbol: PNode, root: TreeNode[ScopeNode[PNode]]): List[(String, Position, Position)] = {
//    def isSymbolInScope(node: TreeNode[ScopeNode[PNode]]): Boolean = {
//      node.value.elements.defs.exists(_ eq symbol)
//    }
//
//    def traverseTree(node: TreeNode[ScopeNode[PNode]], results: List[(String, Position, Position)]): List[(String, Position, Position)] = {
//      val matches = if (isSymbolInScope(node)) {
//        val startPos = nodeStartPosition(packageContexts(node.value.scopeStart.toString).pack, symbol)
//        val endPos = nodeEndPosition(packageContexts(node.value.scopeStart.toString).pack, symbol)
//        if (startPos != null && endPos != null) {
//          List((startPos.source.name, startPos, endPos))
//        } else Nil
//      } else Nil
//
//      // Recurse on children
//      matches ++ node.children.flatMap(child => traverseTree(child, results))
//    }
//
//    traverseTree(root, Nil)
//  }



  private def writeBuiltInPackageToFile(pkg: PPackage): File = {
    import scala.io.Source
    val tempDir = System.getProperty("java.io.tmpdir") // System temp directory
    val fileName = s"builtin_${pkg.packageClause.id.name}.gobra"
    val tempFile = new File(tempDir, fileName)

    if (!tempFile.exists()) {
      try {
        val resourcePath = s"/stubs/${pkg.packageClause.id.name}/${pkg.packageClause.id.name}.gobra" // Path inside JAR
        val inputStream: InputStream = getClass.getResourceAsStream(resourcePath)

        if (inputStream != null) {
          println(s"Copying built-in package from JAR resource: $resourcePath")

          // Read the JAR resource file
          val content = Source.fromInputStream(inputStream).getLines().mkString("\n")
          inputStream.close()

          // Write the content to a local temp file
          val writer = new PrintWriter(tempFile)
          writer.write(content)
          writer.close()
        } else {
          throw new IllegalStateException(s"Built-in Gobra package not found in JAR: $resourcePath")
        }
      } catch {
        case ex: Exception =>
          println(s"Error copying built-in package: ${ex.getMessage}")
          throw ex
      }

      tempFile.setReadOnly() // Set to read-only
    }

    tempFile
  }



  //Function to get go to definition
  def getDefinition(line : Int, column : Int, src : String) : Location = {
    var pkg = findPkgFromSrc(src)

    val s : Source = FileSource(Paths.get(new URI(src)).toString)
    val pos: Position = Position(line, column, s)
    val file : PNode = findFile(pkg, pos)
    val node : PNode = findNode(pkg, file, pos)

    val imp = findImports(pkg, node)
    var defNode = if (imp == null) {
      findDef(pkg, node, line, column)
    } else {
      pkg = imp._1
      imp._2
    }

    if(defNode != null && nodeStartPosition(pkg, defNode).source == null){
      val unq = pkg.imports.filter(_.isInstanceOf[PUnqualifiedImport]).map(_.importPath)
      val realPkg = packageContexts.keys.find(a => unq.contains(a)).get
      pkg = packageContexts(realPkg).pack
      val decs = packageContexts(pkg.packageClause.id.name).pack.declarations

      val realDecs = resolvePMember(decs)
      defNode = realDecs.find(a => a.toString == node.toString).get
    }
    if(defNode == null){
      return null
    }
    val startPos: Position = nodeStartPosition(pkg, defNode)
    val endPos: Position = nodeEndPosition(pkg, defNode)
    val start = new LocPosition(startPos.line - 1, startPos.column - 1) // Line 3, Column 16
    val end = new LocPosition(endPos.line - 1, endPos.column - 1)   // Line 3, Column 20
    val range = new Range(start, end)
    val path = nodeStartPosition(pkg, defNode).source.name
    if(path.substring(0,5) == "stubs"){
      val tempFilePath : File = writeBuiltInPackageToFile(pkg)
      return new Location(tempFilePath.toURI.toString, range)
    }
    val uri = Paths.get(path).toUri.toString

    val location = new Location(uri, range)
    location
  }

  private def findDef(pack: PPackage, node: PNode, line: Int, column: Int) : PNode = {
    val r = packageContexts(pack.packageClause.id.name).root
    val scope: TreeNode[ScopeNode[PNode]] = findScope(pack, node, r, line, column)
    if(scope == null){
      return null
    }
    if(scope.value.elements.referenceMap.contains(node)){
      return scope.value.elements.referenceMap(node)
    }
    val n : Option[PNode] = RecurseForDef(node, scope)

    n match {
      case Some(n) => n
      case None => println("here, means findDef was null?"); null //throw new IllegalStateException("no node found in defs")
    }
  }

  @tailrec
  private def RecurseForDef(node: PNode, treeNode: TreeNode[ScopeNode[PNode]]) : Option[PNode] ={
    val found = checkForNodeInDefs(node, treeNode)
    found match {
      case Some(obj) => Some(obj)
      case None =>
        treeNode.parent match {
          case Some(parent) => RecurseForDef(node, parent)
          case None => None
        }
    }
  }

  //Function to create the ScopeTree Object
  private def makeChildren[R <: PNode, T <: ScopeNode[PNode]](
                                                               pack: PPackage,
                                                               kid: R,
                                                               parent: Option[TreeNode[ScopeNode[PNode]]]
                                                             ): TreeNode[ScopeNode[PNode]] = {
    val kids: Vector[PScope] = findAllScopeChildren(pack, kid)

    if (kids.nonEmpty) {
      // Step 1: Build the ScopeElements without referenceMap
      val elems: ScopeElements = getElems(pack, kid, parent)

      // Step 2: Create the current ScopeNode and TreeNode
      val node: ScopeNode[PNode] = ScopeNode(
        nodeStartPosition(pack, kid).line,
        nodeEndPosition(pack, kid).line,
        elems,
        parent
      )
      var currentNode = TreeNode(node, Vector(), parent)

      // Step 3: Build children recursively
      val grandKids = kids.map { child =>
        makeChildren(pack, child, Some(currentNode))
      }

      // Update children of the current node after recursion
      currentNode.children = grandKids

      // Ensure parent references in children are finalized
      grandKids.foreach { child =>
        child.parent = Some(currentNode)
      }

      // Step 4: Populate the referenceMap for the current node
      val referenceMap: Map[PNode, PNode] = node.elements.vars.collect {
        case v: PIdnUse if resolveDefinition(v, Some(currentNode)) != null =>
          v -> resolveDefinition(v, Some(currentNode))
      }.toMap

      currentNode.value = currentNode.value.copy(elements = currentNode.value.elements.copy(referenceMap = referenceMap))

//      if (parent.isEmpty) {
//        // Root node: Combine defs from all children
//        val combinedDefs = grandKids.flatMap(_.value.elements.defs).distinct
//        val combinedVars = grandKids.flatMap(_.value.elements.vars).distinct
//        //val combinedVars = (currentNode.value.elements.vars ++ grandKids.flatMap(_.value.elements.vars)).distinct
//        val combinedReferenceMap = grandKids.flatMap(_.value.elements.referenceMap).toMap
//        currentNode.value = currentNode.value.copy(
//          elements = currentNode.value.elements.copy(
//            defs = combinedDefs,
//            //vars = combinedVars,
//            referenceMap = combinedReferenceMap
//          )
//        )
//      }

      currentNode
    } else {
      // Leaf node creation
      val scopeS = nodeStartPosition(pack, kid).line
      val scopeE = nodeEndPosition(pack, kid).line
      val elems = getElems(pack, kid, parent)
      val leaf: ScopeNode[PNode] = ScopeNode(scopeS, scopeE, elems, parent)

      TreeNode(leaf, Vector(), parent)
    }
  }



  private def findAllScopeChildren(pack: PPackage, node: PNode): Vector[PScope] = {
    val children = safeChild(node, pack)
    val scopeChildren = children.filter(_.isInstanceOf[PScope])
    val nonScopeChildren = children.filter(!_.isInstanceOf[PScope])
    (scopeChildren ++ nonScopeChildren.flatMap(child => findAllScopeChildren(pack, child))).map(_.asInstanceOf[PScope])
  }

  private def findLeaves(pack: PPackage, node: PNode, isInitialCall: Boolean = true): Vector[PNode] = {
    val children = safeChild(node, pack)
    if (children.isEmpty) {
      Vector(node)
    } else {
      if(!isInitialCall && node.isInstanceOf[PScope]){
        node match {
          case decl: PFunctionDecl =>
            Vector(decl.id)
          case x =>
            Vector(x)
        }
      }else{
        Vector(node) ++ children.flatMap(child => findLeaves(pack, child, isInitialCall = false))
      }
    }
  }

  private def getElems(pack: PPackage, scope: PNode, parent: Option[TreeNode[ScopeNode[PNode]]]): ScopeElements = {
    val elements: Vector[PNode] = findLeaves(pack, scope)

    val defsAndUnkFilter: PNode => Boolean = x =>
      x.isInstanceOf[PIdnDef] || x.isInstanceOf[PIdnUnk]

    val usesFilter: PNode => Boolean = x =>
      x.isInstanceOf[PIdnDef] || x.isInstanceOf[PIdnUnk] || x.isInstanceOf[PIdnUse]

    val parentVars = parent.map(_.value.elements.vars).getOrElse(Vector()) // 🔹 Inherit parent vars
    val parentDefs = parent.map(_.value.elements.defs).getOrElse(Vector()) // 🔹 Inherit parent defs

    // Collect defs and vars without the referenceMap
    val defs = parent match {
      case Some(p) =>
        elements.filter(x => defsAndUnkFilter(x) && !p.value.elements.defs.exists(_ eq x))
      case None =>
        elements.filter(defsAndUnkFilter)
    }

    val localVars = elements.filter(usesFilter)
    val inheritedVars = parentVars.filterNot(pVar => localVars.exists(lVar => lVar eq pVar))
    val vars = localVars// ++ inheritedVars

    // Create the ScopeElements without the referenceMap
    ScopeElements(defs, vars, Map.empty)
  }


  @tailrec
  private def resolveDefinition(variable: PIdnUse, parent: Option[TreeNode[ScopeNode[PNode]]]): PNode = {
    parent match {
      case Some(scopeNode) =>
        // Check if the variable is in the current scope
        scopeNode.value.elements.defs.find(_.toString == variable.toString) match {
          case Some(definition) => definition
          case None => resolveDefinition(variable, scopeNode.parent) // Traverse upwards
        }
      case None => null // No definition found (possible built-in or error case)
    }
  }


  private def findFile(pack: PPackage, pos: Position) : PNode = {
    val children = safeChild(pack, pack)
    val child = children.find(p => nodeStartPosition(pack, p).source == pos.source && p.isInstanceOf[PScope])
    child match {
      case Some(c) => c
      case None => throw new IllegalStateException("No matching file")
    }
  }

  private def findNode(pack: PPackage, node: PNode, pos : Position) : PNode = {

    var n : PNode = node
    val children = safeChild(node, pack)
    children.foreach { c =>
      if(isAfter(pos, nodeStartPosition(pack, c)) && isAfter(nodeEndPosition(pack, c), pos)){
        n = findNode(pack, c, pos)
      }
    }
    n
  }

  private def findScope(pkg: PPackage, toFind: PNode, node: TreeNode[ScopeNode[PNode]], line: Int, column: Int): TreeNode[ScopeNode[PNode]] = {
    // If we are at the package root, first select the correct file subtree
    //val child = children.find(p => nodeStartPosition(pack, p).source == pos.source && p.isInstanceOf[PScope])
//    if (node.parent.isEmpty) { // Root node for the package
//      val fileSource = nodeStartPosition(pkg, toFind).source.name // Get the source URI of the target node
//      println(s"fileSource: $fileSource")
//      // Find the correct file subtree by comparing its source URI
//      val fileNodeOpt = node.children.find { fileNode =>
//        val fileStartPos = nodeStartPosition(pkg, fileNode.value.elements.vars.headOption.getOrElse(fileNode.value)) // Use the first def as a reference
//        println(s"fileStartPos: $fileStartPos")
//        fileStartPos.source.name == fileSource
//      }
//      println(s"fileNodeOpt: $fileNodeOpt")
//      fileNodeOpt match {
//        case Some(fileNode) => return findScope(pkg, toFind, fileNode, line, column) // Continue searching within the correct file subtree
//        case None => return null // No matching file found
//      }
//    }
    val n = node
    val children = node.children
    if(n.value.elements.vars.exists(_ eq toFind)){
      return n
    }
    for (c <- children){
      if(c.value.scopeStart <= line && line <= c.value.scopeEnd){
        val found = findScope(pkg, toFind, c, line, column)
        if (found != null) {
          return found // Return as soon as we find a match
        }
      }
    }
    null
  }


  private case class ScopeNode[+T](
                                    scopeStart: Int,
                                    scopeEnd: Int,
                                    elements: ScopeElements,
                                    parent: Option[TreeNode[ScopeNode[PNode]]]
                                  ) {
    override def toString: String = s"ScopeNode(scopeStart = $scopeStart, scopeEnd = $scopeEnd, defs = ${elements.defs}, vars = ${elements.vars})"
  }

  private case class ScopeElements(
                            defs: Vector[PNode],  // Definitions in this scope
                            vars: Vector[PNode],  // Variable references in this scope
                            referenceMap: Map[PNode, PNode] // Maps variable references to their definitions
                          )

}


