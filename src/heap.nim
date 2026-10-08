## Leftist heap — priority queue for best-first search (issue #13)
##
## A leftist heap is a mergeable priority queue with O(log n) operations.
## Used to order the search worklist by cost (ascending), giving best-first
## search instead of DFS/LIFO.
##
## Based on Okasaki "Purely Functional Data Structures" §3.5.

type
  HeapNode*[T] = ref object
    rank*: int
    key*: float  # cost; lower = higher priority
    value*: T
    left*, right*: HeapNode[T]

  LeftistHeap*[T] = object
    root*: HeapNode[T]
    size*: int

proc rank[T](n: HeapNode[T]): int =
  if n == nil: 0 else: n.rank

proc makeNode[T](key: float, value: T, left, right: HeapNode[T]): HeapNode[T] =
  let r = rank(right) + 1
  # Ensure leftist invariant: rank(left) >= rank(right)
  if rank(left) >= rank(right):
    HeapNode[T](rank: r, key: key, value: value, left: left, right: right)
  else:
    HeapNode[T](rank: r, key: key, value: value, left: right, right: left)

proc merge[T](a, b: HeapNode[T]): HeapNode[T] =
  if a == nil: return b
  if b == nil: return a
  if a.key <= b.key:
    makeNode(a.key, a.value, a.left, merge(a.right, b))
  else:
    makeNode(b.key, b.value, b.left, merge(a, b.right))

proc initHeap*[T](): LeftistHeap[T] =
  LeftistHeap[T](root: nil, size: 0)

proc isEmpty*[T](h: LeftistHeap[T]): bool =
  h.root == nil

proc len*[T](h: LeftistHeap[T]): int =
  h.size

proc insert*[T](h: var LeftistHeap[T], key: float, value: T) =
  let node = HeapNode[T](rank: 1, key: key, value: value, left: nil, right: nil)
  h.root = merge(h.root, node)
  inc h.size

proc peek*[T](h: LeftistHeap[T]): tuple[key: float, value: T] =
  assert h.root != nil, "peek on empty heap"
  (h.root.key, h.root.value)

proc pop*[T](h: var LeftistHeap[T]): tuple[key: float, value: T] =
  assert h.root != nil, "pop on empty heap"
  result = (h.root.key, h.root.value)
  h.root = merge(h.root.left, h.root.right)
  dec h.size

when isMainModule:
  var h = initHeap[string]()
  h.insert(3.0, "three")
  h.insert(1.0, "one")
  h.insert(2.0, "two")
  
  assert h.pop().value == "one"
  assert h.pop().value == "two"
  assert h.pop().value == "three"
  assert h.isEmpty()
  echo "ok: leftist heap works"
