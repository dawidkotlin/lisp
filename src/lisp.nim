import strutils, tables, terminal, hashes, sequtils

type
  NodeKind = enum nkCall, nkNum, nkSym, nkStr, nkProc, nkTable
  Node = ref object
    case kind: NodeKind
    of nkCall: discard
    of nkNum: numVal: float
    of nkStr: strVal: string
    of nkSym: symVal: string
    of nkProc: procVal: proc(nodes: seq[Node]): Node
    of nkTable: tableVal: Table[Hash, Node]
    kids: seq[Node]

proc newProc(procVal: proc(nodes: seq[Node]): Node): Node =
  result = Node(kind: nkProc, procVal: procVal)

proc newNum(numVal: float): Node =
  result = Node(kind: nkNum, numVal: numVal)

proc newStr(strVal: string): Node =
  result = Node(kind: nkStr, strVal: strVal)

proc newSym(symVal: string): Node =
  result = Node(kind: nkSym, symVal: symVal)

proc treeRepr(node: Node): string =
  if node == nil:
    result = "[ NIL ]"
  else:
    case node.kind
    of nkNum: result = $node.numVal
    of nkStr: result = '"' & $node.strVal & '"'
    of nkSym: result = $node.symVal
    of nkProc: result = "[ BUILTIN PROC ]"
    of nkTable:
      result = "[ TABLE ]"
      # result = "{"
      # for k, v in node.tableVal:
      #   result.add k & ": " & v.treeRepr() & ", "
      # result.delete result.high-1, result.high
      # result.add "}"
    of nkCall:
      result = "("
      for kidi, kid in node.kids:
        result.add kid.treeRepr()
        if kidi != node.kids.high:
          result.add ' '
      result.add ')'

var
  globals: Table[string, Node] # Definitely no symbols as values
  locals: seq[Table[string, Node]] # Definitely no symbols as values

proc eval(node: Node): Node =
  ## Evalues symbols, executes calls, leaves rest untouched...
  case node.kind
  of nkStr, nkNum, nkProc, nkTable:
    result = node
  of nkCall:
    let first = eval(node.kids[0])
    # assert first.kind == nkProc, '\n' & $first.kind & '\n' & first.treeRepr()
    result = first.procVal(if node.kids.len < 2: @[] else: node.kids[1..^1])
  of nkSym:
    for i in countdown(locals.high, 0):
      if node.symVal in locals[i]:
        result = locals[i][node.symVal] # I'm not expecting symbols here!
        break
    if result == nil:
      if node.symVal in globals:
        result = globals[node.symVal] # I'm not expecting symbols here!
      else:
        quit "Symbol has no value: " & node.symVal
    assert result != nil
    assert result.kind != nkSym

proc parse(code: string): Node =
  var i = 0
  var scopes: seq[Node]
  while i <= code.high:
    case code[i]
    of '(':
      scopes.add Node(kind: nkCall)
      if result == nil:
        result = scopes[^1]
      inc i
    of ')':
      if scopes.len > 1:
        scopes[^2].kids.add scopes[^1]
      scopes.del scopes.high
      inc i
    of Whitespace:
      inc i
    else:
      var token: string
      while i <= code.high and code[i] notin Whitespace + {'(', ')'}:
        token.add code[i]
        inc i
      if token[0] in Digits:
        scopes[^1].kids.add newNum(token.parseFloat())
      elif token[0] in {'"', '\''}:
        assert token[0] == token[^1]
        scopes[^1].kids.add newStr(token[1..^2])
      else:
        scopes[^1].kids.add newSym(token)      

proc hash(node: Node): Hash =
  var h = 0
  let node = node.eval()
  h = h !& node.kind.hash()
  case node.kind
  of nkNum: h = h !& node.numVal.hash()
  of nkStr: h = h !& node.strVal.hash()
  else: quit $node.kind
  result = !$h

proc resetState =
  locals = newSeq[Table[string, Node]](1)
  globals.reset()

  globals["+"] = newProc proc(nodes: seq[Node]): Node =
    result = newNum(0)
    for n in nodes:
      result.numVal += n.eval().numVal

  globals["-"] = newProc proc(nodes: seq[Node]): Node =
    result = newNum(0)
    for n in nodes:
      result.numVal -= n.eval().numVal

  globals["*"] = newProc proc(nodes: seq[Node]): Node =
    result = newNum(1)
    for n in nodes:
      result.numVal *= n.eval().numVal

  globals["/"] = newProc proc(nodes: seq[Node]): Node =
    result = newNum(1)
    for n in nodes:
      result.numVal /= n.eval().numVal

  globals["global"] = newProc proc(nodes: seq[Node]): Node =
    globals[nodes[0].symVal] = nodes[1].eval()

  globals["do"] = newProc proc(nodes: seq[Node]): Node =
    for i in 0 ..< nodes.high:
      discard nodes[i].eval()
    result = nodes[^1].eval()

  globals["echo"] = newProc proc(nodes: seq[Node]): Node =
    for n in nodes:
      echo n.treeRepr()

  globals["join"] = newProc proc(nodes: seq[Node]): Node =
    result = newStr("")
    for n in nodes:
      result.strVal.add n.eval().strVal

  # globals["let"] = newProc proc(nodes: seq[Node]): Node =
  #   var table: Table[string, Node]
  #   for i in countup(0, nodes.high-2, 2):
  #     assert i+1 <= nodes.high
  #     table[nodes[i].symVal] = nodes[i+1].eval()
  #   locals.add table
  #   result = nodes[^1].eval() # ???
  #   locals.del locals.high

  globals["func"] = newProc proc(outer: seq[Node]): Node =
    result = newProc proc(inner: seq[Node]): Node =
      var table: Table[string, Node]
      for i in 0 ..< outer.high:
        # if i == outer.high-1 and outer[i].symVal.startsWith("..."):
        #   let args = Node(kind: nkTable)
        #   var argi = 0'f64
        #   for inneri in i..inner.high:
        #     args.tableVal[newNum(argi)] = inner[inneri]
        #     argi += 1
        #   table[outer[i].symVal] = args
        # else:
        table[outer[i].symVal] = inner[i].eval()
      locals.add table
      result = outer[^1].eval()
      locals.del locals.high

  globals["table"] = newProc proc(nodes: seq[Node]): Node =
    result = Node(kind: nkTable)
    for i in countup(0, nodes.high-1, 2):
      result.tableVal[nodes[i].eval().hash()] = nodes[i+1].eval()

  globals["get"] = newProc proc(nodes: seq[Node]): Node =
    result = nodes[0].eval().tableVal[nodes[1].eval().hash()]

  globals["let"] = newProc proc(nodes: seq[Node]): Node =
    locals[^1][nodes[0].symVal] = nodes[1].eval()

  globals["scope"] = newProc proc(nodes: seq[Node]): Node =
    locals.setLen locals.len+1
    for n in nodes:
      discard n.eval()
    locals.setLen locals.len-1

template check(a, b) =
  assert a == b, $a

resetState()
check "(+ 2 3)".parse().eval().numVal, 5
check "(+ (+ 1 1) 3)".parse().eval().numVal, 5
check "(do (global x 2) (global y 3) (+ x y))".parse().eval().numVal, 5
check """(join "foo" "bar" "baz")""".parse().eval().strVal, "foobarbaz"
check "(scope (let a 1) (let b 2) (+ a b))".parse().eval().numVal, 3
# check "(+ (let a 1 b 2 (+ a b)) (let a 10 b 20 (+ a b)))".parse().eval().numVal, 33
# check "(let a 5 (+ (let a 10 (+ a 1)) a))".parse().eval().numVal, 16
# check "((func x y (+ x y)) 1 2)".parse().eval().numVal, 3
# check "(let localFoo (func x y (+ x y)) (localFoo 1 2))".parse().eval().numVal, 3
# check "(do (global globalFoo (func x y (+ x y))) (globalFoo 1 2))".parse().eval().numVal, 3
# assert "(let myTable (table 'a' 1 'b' 2 'c' 3))".parse().eval() == nil
# check "(get myTable 'a')".parse().eval().numVal, 1
# check "(get myTable 'b')".parse().eval().numVal, 2
# check "(get myTable 'c')".parse().eval().numVal, 3

resetState()
stdout.styledWriteLine styleBright, fgYellow, "REPL ready"
var buf: string
while true:
  buf.add (try: stdin.readLine() except EOFError: break)
  var open, close = 0
  for ch in buf:
    if ch == '(': inc open
    else: inc close
  if close >= open:
    stdout.styledWriteLine styleBright, fgBlue, buf.parse().eval().treeRepr()
    buf = ""