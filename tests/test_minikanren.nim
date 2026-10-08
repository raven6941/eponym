## Tests for the independent relational engine (minikanren.nim) — Track C
import minikanren

# Unification: v1 = 42, v2 = v1  =>  v2 = 42
let v1 = freshVar()
let v2 = freshVar()
let g = conj(`==`(v1, rint(42)), `==`(v2, v1))
let res = run(v2, g, 5)
assert res.len == 1
assert res[0].kind == rkAtom and res[0].name == "42"
echo "ok: unification (v1=42, v2=v1 => v2=42)"

# Pair unification
let a = freshVar()
let b = freshVar()
let g2 = `==`(rpair(a, b), rpair(rint(1), rint(2)))
let res2 = run(a, g2, 5)
assert res2.len == 1 and res2[0].name == "1"
echo "ok: pair unification"

# Occurs check: v = (v) should fail (no infinite term)
let v3 = freshVar()
let g3 = `==`(v3, rpair(v3, rnil()))
let res3 = run(v3, g3, 5)
assert res3.len == 0
echo "ok: occurs check prevents cyclic term"

echo "--- all minikanren tests passed ---"
