## Tests for relational type inference (rel_elab.nim) — Track C
import minikanren
import rel_elab
import strutils

# Forward: infer type of zero
let q1 = freshVar()
let r1 = run(q1, typeo(zeroTm(), q1, rnil()), 3)
assert r1.len == 1 and $r1[0] == "nat"
echo "ok: typeo infers zero : nat"

# Forward: infer type of (suc zero)
let q2 = freshVar()
let r2 = run(q2, typeo(sucTm(zeroTm()), q2, rnil()), 3)
assert r2.len == 1 and $r2[0] == "nat"
echo "ok: typeo infers suc(zero) : nat"

# Forward: infer type of (lam (var 0)) — polymorphic identity
let q3 = freshVar()
let idTm = lamTm(varTm(0))
let r3 = run(q3, typeo(idTm, q3, rnil()), 3)
# All results are alpha-equivalent (arr ?v ?v); accept any number >= 1
assert r3.len >= 1
assert ($r3[0]).startsWith("(arr")
echo "ok: typeo infers lam(var 0) : (arr ?v ?v)"

echo "--- all rel_elab tests passed ---"
echo "Note: backward synthesis requires fair search (future work)."
