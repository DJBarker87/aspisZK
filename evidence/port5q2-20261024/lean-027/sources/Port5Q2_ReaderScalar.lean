import Port5Q2_ReaderRaw
import Port1_LibrarySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderScalar
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Raw := (N : Usize) → verifier.Reader → Result (Array U8 N × verifier.Reader)
def readK (raw : Raw) (decode : Slice U8 → Result (Option aspis_core.field.QM31))
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.QM31 verifier.Error) ×
    verifier.Reader)
  := do
  let (a, self1) ← raw 16#usize self
  let s ← lift (Array.to_slice a)
  let o ← decode s
  let r ← Port1_LibrarySource.okOr o verifier.Error.Checkpoint
  ok (r, self1)

def decodeK (s : Slice U8) : Result (Option aspis_core.field.QM31) := do
  let value ← OraclePortCkptAbi2Extracted.decode_k_spec s
  ok (value.map CheckpointBytes3Namespaces.fromK)

theorem reference_k (r : verifier.Reader) :
    readK CheckpointBytes3Reader.raw decodeK r=CheckpointBytes3Reader.readK r := by
  unfold readK decodeK CheckpointBytes3Reader.readK
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair success
  rcases pair with ⟨bytes,out⟩
  try dsimp only
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro value decoded
  cases value <;> rfl

#print axioms reference_k
def readE (raw : Raw) (decode : Slice U8 → Result (Option aspis_core.field.wide_exact.WideExact))
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.wide_exact.WideExact
    verifier.Error) × verifier.Reader)
  := do
  let (a, self1) ← raw 32#usize self
  let s ← lift (Array.to_slice a)
  let o ← decode s
  let r ← Port1_LibrarySource.okOr o verifier.Error.Checkpoint
  ok (r, self1)

def decodeE (s : Slice U8) : Result (Option aspis_core.field.wide_exact.WideExact) := do
  let value ← OraclePortCkptAbi2Extracted.decode_e_spec s
  ok (value.map CheckpointBytes3Namespaces.fromE)

theorem reference_e (r : verifier.Reader) :
    readE CheckpointBytes3Reader.raw decodeE r=CheckpointBytes3Reader.readE r := by
  unfold readE decodeE CheckpointBytes3Reader.readE
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair success
  rcases pair with ⟨bytes,out⟩
  try dsimp only
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro value decoded
  cases value <;> rfl

#print axioms reference_e

/-- Bounded CURRENT scalar helper with an arbitrary debug panic handler.
The field codec is the separately certified concrete content interpretation. -/
theorem current_k
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (bound : r.at.val+16≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096) :
    readK (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) decodeK r=CheckpointBytes3Reader.readK r := by
  rw [← reference_k r]
  unfold readK
  dsimp only
  rw [Port5Q2_ReaderRaw.reference 16#usize (unwrap 16#usize) (unwrap_ok 16#usize) r bound size]

#print axioms current_k

/-- Bounded CURRENT scalar helper with an arbitrary debug panic handler.
The field codec is the separately certified concrete content interpretation. -/
theorem current_e
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (bound : r.at.val+32≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096) :
    readE (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) decodeE r=CheckpointBytes3Reader.readE r := by
  rw [← reference_e r]
  unfold readE
  dsimp only
  rw [Port5Q2_ReaderRaw.reference 32#usize (unwrap 32#usize) (unwrap_ok 32#usize) r bound size]

#print axioms current_e
end AspisR1.Port5Q2_ReaderScalar
end
