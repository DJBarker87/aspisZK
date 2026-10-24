import Port5Q2_ReaderRaw
import CheckpointBytes4RawFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Roots
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Raw := (N : Usize) → verifier.Reader → Result (Array U8 N × verifier.Reader)
/-- Exactly the state/root roots of the current op18 tail, starting at80. -/
def roots (raw : Raw) (bytes : Slice U8) := do
  let (state,r) ← raw 32#usize ⟨bytes,80#usize⟩
  let (root0,r1) ← raw 32#usize r
  let (root1,r2) ← raw 32#usize r1
  ok (state,root0,root1,r2)

theorem reference
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (room : 176≤bytes.val.length) (size : bytes.val.length≤4096) :
    roots (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) bytes =
      roots CheckpointBytes3Reader.raw bytes := by
  unfold roots
  dsimp only
  rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) ⟨bytes,80#usize⟩ (by change 80+32≤_; omega) size]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨state,r⟩
  dsimp only
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success
    32#usize ⟨bytes,80#usize⟩ r state (by change 80+32≤_; omega) called
  dsimp only at cursor backing
  rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) r
    (by rw [backing,cursor]; change 80+32+32≤_; omega) (by rw [backing]; exact size)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called1
  rcases pair with ⟨root0,r1⟩
  dsimp only
  obtain ⟨contents1,cursor1,backing1⟩ := CheckpointBytes4RawFields.raw_success
    32#usize r r1 root0 (by rw [backing,cursor]; change 80+32+32≤_; omega) called1
  rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap _) (unwrap_ok _) r1
    (by rw [backing1,backing,cursor1,cursor]; change 80+32+32+32≤_; omega)
    (by rw [backing1,backing]; exact size)]

#print axioms reference
end AspisR1.Port6CK_Roots
end
