import CuSavingsRetainedClaimBinding
import AspisR1CanonicalFieldStream.FunsExternal
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedClaimBindingSelector
open Aeneas Aeneas.Std Result
namespace R
abbrev K := AspisR1RhoPowerTail.aspis_core.field.QM31
end R
abbrev K := AspisR1CanonicalDots.field.QM31
/-- Coordinate transport only; no reduction or validation is added. -/
def toDot (x : R.K) : K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
/-- The source `prepared_claim` match, retaining every checked array read and
its same final-message field decoder. The point parameter is not assumed valid. -/
def scalar {H : Type} (sem : AspisR1RhoPowerTail.r1_semantic.Verified H)
    (y1 : Slice U8) (point l : Usize) : Result K := do
  if point.val ≤ 2 then
    let row ← Array.index_usize sem.claims point
    let x ← Array.index_usize row l
    .ok (toDot x)
  else if point = 3#usize then
    let x ← Array.index_usize sem.extra l
    .ok (toDot x)
  else if point = 4#usize then
    let x ← Array.index_usize sem.before_z1 l
    .ok (toDot x)
  else
    let x ← AspisR1CanonicalDots.weights.field y1 l
    .ok x.c0

def decode (bytes : Slice U8) : Result (Option K) := do
  let x ← AspisR1CuRho.field.QM31.from_le_bytes bytes
  .ok (x.map fun q => ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩)

@[reducible] def select {H : Type} (sem : AspisR1RhoPowerTail.r1_semantic.Verified H)
    (y1 : Slice U8) (point : Usize) : AspisR1CanonicalDots.VectorCommon where
  decode := decode
  claimScalar := scalar sem y1 point

theorem selected {H : Type} (sem : AspisR1RhoPowerTail.r1_semantic.Verified H)
    (y1 : Slice U8) (point l : Usize) :
    (select sem y1 point).claimScalar l = scalar sem y1 point l := rfl

#print axioms select
#print axioms selected
end AspisR1.CuSavingsRetainedClaimBindingSelector
