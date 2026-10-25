import T2Nat_Try
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_RawStage
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq
abbrev Raw := Port5Q2_ReaderScalar.Raw
abbrev Digest := Array U8 32#usize

def body {A : Type} (raw : Raw) (comparison : Result Bool)
    (k : Digest → Digest → Digest → verifier.Reader → Result (core.result.Result A verifier.Error))
    (r : verifier.Reader) : Result (core.result.Result A verifier.Error) := do
  let different ← comparison
  if different then ok (.Err .Checkpoint) else
    let (state,r1) ← raw 32#usize r
    let (root0,r2) ← raw 32#usize r1
    let (root1,r3) ← raw 32#usize r2
    k state root0 root1 r3

/-- A small generic cut keeps the raw-array implementation out of the
kernel's repeated congruence normalization. -/
theorem congr {A : Type} (left right : Raw) (same : ∀ N r, EqOk (left N r) (right N r))
    (comparison : Result Bool)
    (k l : Digest → Digest → Digest → verifier.Reader → Result (core.result.Result A verifier.Error))
    (next : ∀ a b c r, EqOk (k a b c r) (l a b c r)) (r : verifier.Reader) :
    EqOk (body left comparison k r) (body right comparison l r) := by
  unfold body
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl comparison)
  intro different
  cases different with
  | true => exact T2Nat_ResultEq.refl _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply T2Nat_ResultEq.bind (same _ _)
    rintro ⟨state,r1⟩
    apply T2Nat_ResultEq.bind (same _ _)
    rintro ⟨root0,r2⟩
    apply T2Nat_ResultEq.bind (same _ _)
    rintro ⟨root1,r3⟩
    exact next state root0 root1 r3

#print axioms congr
end AspisR1.T2Nat_RawStage
end
