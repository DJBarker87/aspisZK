import R1Z.ProverRwEntropyResume64
import R1Z.ProverRwEntropyAbort64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyDecode64
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectPrefix ProverRwEntropyHalves ProverCommitOwnerZero42
attribute [local instance] Classical.propDecidable

def field (bytes : Array U8 64#usize) : Bytes :=
  ⟨bytes.val.take 32,by simp [bytes.property]⟩
def leaf (bytes : Array U8 64#usize) : Bytes :=
  ⟨bytes.val.drop 32,by simp [bytes.property]⟩

theorem split_join (bytes : Array U8 64#usize) : join (field bytes) (leaf bytes) = bytes := by
  apply Subtype.ext
  exact List.take_append_drop 32 bytes.val

def raw (bytes : Array U8 64#usize) : ProverCommitPublicNonce40.Raw :=
  Fin.cases (ProverCommitOwnerBytes42.block (field bytes))
    (fun _ => ProverCommitOwnerBytes42.block (leaf bytes))

theorem raw_zero_iff (bytes : Array U8 64#usize) :
    (∃ i, raw bytes i = 0) ↔
      ProverCommitOwnerBytes42.block (field bytes) = 0 ∨
      ProverCommitOwnerBytes42.block (leaf bytes) = 0 := by
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

variable [ExternalTypes]
/-- Every full successful reply is split by the actual emitted slice/copy
operations and tested by the model's two-seed decoder. There is no assumed
successful read, decoded-output equality, or per-reply nonzero premise. -/
theorem after_full (ops : ExternalFuns) (nonce : Bytes) (retry : Usize)
    (bytes : Array U8 64#usize) :
    letI : ExternalFuns := install ops
    after nonce retry back (.Ok (),Array.to_slice bytes) =
      if ProverCommitPublicNonce40.decode (raw bytes) = none then
        .ok (.cont (Usize.wrapping_add retry 1#usize))
      else .ok (.done (.Ok ⟨nonce,field bytes,leaf bytes⟩)) := by
  letI : ExternalFuns := install ops
  have joined := ProverRwEntropyResume64.after_join ops nonce retry (field bytes) (leaf bytes)
  rw [split_join] at joined
  simpa only [ProverRwEntropyAbort64.decode_none_iff,raw_zero_iff] using joined

#print axioms split_join
#print axioms raw_zero_iff
#print axioms after_full
end R1Z.ProverRwEntropyDecode64
