import strutils, tables, terminal, hashes, sequtils

type
  NodeKind = enum nkCall, nkNum, nkSym, nkStr, nkProc, nkTable, nkSeq
  Node = ref object
    case kind: NodeKind
    of nkCall: discard
    of nkNum: numVal: float
    of nkStr: strVal: string
    of nkSym: symVal: string
    of nkProc: procVal: proc(nodes: seq[Node]): Node
    of nkTable: tableVal: Table[Hash, Node]
    of nkSeq: seqVal: seq[Node]
    kids: seq[Node]
    methods: Table[string, proc(args: seq[Node]): Node]

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
    of nkSeq:
      result = "[ SEQ ]"
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
  of nkStr, nkNum, nkProc, nkTable, nkSeq:
    result = node
  of nkCall:
    let kid0 = node.kids[0].eval()
    if kid0.kind == nkProc:
      result = kid0.procVal(if node.kids.len == 1: @[] else: node.kids[1..^1])
    else:
      assert node.kids.len > 1
      let obj = kid0
      let procName = node.kids[1]
      let args = if node.kids.len > 2: @[obj] & node.kids[2..^1] else: @[obj]
      result = obj.methods[procName.symVal](args) # WRONG?
  of nkSym:
    for i in countdown(locals.high, 0):
      if node.symVal in locals[i]:
        result = locals[i][node.symVal] # I'm not expecting symbols here!
        break
    if result == nil:
      if node.symVal in globals:
        result = globals[node.symVal] # I'm not expecting symbols here!
      else:
        raiseAssert "Undefined symbol: " & node.symVal
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

  # globals["do"] = newProc proc(nodes: seq[Node]): Node =
  #   for i in 0 ..< nodes.high:
  #     discard nodes[i].eval()
  #   result = nodes[^1].eval()

  globals["echo"] = newProc proc(nodes: seq[Node]): Node =
    for n in nodes:
      echo n.eval().treeRepr()

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

  globals["newTable"] = newProc proc(nodes: seq[Node]): Node =
    result = Node(kind: nkTable)
    for i in countup(0, nodes.high-1, 2):
      result.tableVal[nodes[i].eval().hash()] = nodes[i+1].eval()

    result.methods["get"] = proc(nodes: seq[Node]): Node =
      result = nodes[0].eval().tableVal[nodes[1].eval().hash()]

    result.methods["set"] = proc(nodes: seq[Node]): Node =
      nodes[0].eval().tableVal[nodes[1].eval().hash()] = nodes[2].eval()

  globals["newSeq"] = newProc proc(nodes: seq[Node]): Node =
    result = Node(kind: nkSeq)
    result.seqVal.setLen nodes.len
    for i in 0 .. nodes.high:
      result.seqVal[i] = nodes[i].eval()
    
    result.methods["get"] = proc(nodes: seq[Node]): Node =
      result = nodes[0].eval().seqVal[nodes[1].eval().numVal.int]

    result.methods["set"] = proc(nodes: seq[Node]): Node =
      nodes[0].eval().seqVal[nodes[1].eval().numVal.int] = nodes[2].eval()

  globals["."] = newProc proc(nodes: seq[Node]): Node =
    var args = @[nodes[0]]
    if nodes.len > 2:
      args.add nodes[2..^1]
    result = nodes[0].eval().methods[nodes[1].symVal](args)

    # # [ 0       1    2    ]
    # "(. myTable get 'b')"

  globals["="] = newProc proc(nodes: seq[Node]): Node =
    locals[^1][nodes[0].symVal] = nodes[1].eval()

  globals["scope"] = newProc proc(nodes: seq[Node]): Node =
    locals.setLen locals.len+1
    for i in 0 ..< nodes.high:
      discard nodes[i].eval()
    result = nodes[^1].eval()
    locals.setLen locals.len-1

  # globals["forEach"] = newProc proc(nodes: seq[Node]): Node =
    
template check(a, b) =
  assert a == b, $a

resetState()
check "(+ 2 3)".parse().eval().numVal, 5
check "(+ (+ 1 1) 3)".parse().eval().numVal, 5
check "(scope (scope (global x 2) (global y 3)) (+ x y)".parse().eval().numVal, 5
check """(join "foo" "bar" "baz")""".parse().eval().strVal, "foobarbaz"
check "(scope (= a 1) (= b 2) (+ a b))".parse().eval().numVal, 3
check "(+ (scope (= a 1) (= b 2) (+ a b)) (scope (= a 10) (= b 20) (+ a b)))".parse().eval().numVal, 33
check "(scope (= a 5) (+ (scope (= a 10) (+ a 1)) a))".parse().eval().numVal, 16
check "((func x y (+ x y)) 1 2)".parse().eval().numVal, 3
check "(scope (= localFoo (func x y (+ x y))) (localFoo 1 2))".parse().eval().numVal, 3
check "(scope (scope (global globalFoo (func x y (+ x y)))) (globalFoo 1 2))".parse().eval().numVal, 3
discard "(= myTable (newTable 'a' 1 'b' 2 'c' 3))".parse().eval()
check "(myTable get 'a')".parse().eval().numVal, 1
check "(myTable get 'b')".parse().eval().numVal, 2
check "(myTable get 'c')".parse().eval().numVal, 3
discard "(myTable set 'c' 123)".parse().eval()
check "(myTable get 'c')".parse().eval().numVal, 123
discard "(= mySeq (newSeq 'foo' 'bar' 'baz'))".parse().eval()
check "(mySeq get 0)".parse().eval().strVal, "foo"
check "(mySeq get 1)".parse().eval().strVal, "bar"
check "(mySeq get 2)".parse().eval().strVal, "baz"
discard "(mySeq set 2 'foobarbaz')".parse().eval()
check "(mySeq get 2)".parse().eval().strVal, "foobarbaz"

check "+ 2 3".parse().eval().numVal, 5

resetState()
stdout.styledWriteLine styleBright, fgYellow, "REPL ready"
var buf: string
while true:
  stdout.styledWrite fgGreen, ">> "
  let input = try: stdin.readLine() except EOFError: break
  if input != "":
    buf.add input
    var open, close = 0
    for ch in buf:
      if ch == '(': inc open
      else: inc close
    if close >= open:
      try:
        let result = buf.parse().eval()
        stdout.styledWriteLine styleBright, fgBlue, result.treeRepr()
      except Exception as err:
        stderr.styledWriteLine styleBright, fgRed, "ERROR", resetStyle, " ", err.msg
      buf = ""