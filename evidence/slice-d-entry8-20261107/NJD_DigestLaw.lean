import NFY_Part005
set_option autoImplicit false
noncomputable section
namespace NJD_DigestLaw
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Digest := Array U32 8#usize
open NFY_NBP_DecodeWord
attribute [local instance] Classical.propDecidable

def mapped (bytes : Array U8 32#usize) : core.result.Result Digest PE :=
  match NFY_NBP_DigestDecode.decoded bytes with
  | .Ok v => .Ok v
  | .Err _ => .Err .InvalidAccountData

def canonical (bytes : Array U8 32#usize) : Prop :=
  word bytes 0 < P ∧ word bytes 1 < P ∧ word bytes 2 < P ∧ word bytes 3 < P ∧
  word bytes 4 < P ∧ word bytes 5 < P ∧ word bytes 6 < P ∧ word bytes 7 < P

def stub (bytes : Array U8 32#usize) : core.result.Result Digest PE :=
  if canonical bytes then .Ok (NFY_NBG_WideBytes.limbs bytes) else .Err .InvalidAccountData

/-- Complete CLOSED digest decoder followed by the frozen caller's map_err.
No canonical-input assumption, no chosen successful reply, and no field product. -/
theorem mapped_source (bytes : Array U8 32#usize) :
    (do let r ← atomic_statement.decode_digest_canonical bytes
        ok (match r with
          | .Ok v => core.result.Result.Ok v
          | .Err _ => .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) = ok (mapped bytes) := by
  rw [NFY_NBP_DigestDecode.result]
  rfl

/-- Native NJD_lane.decode computes this all-eight-word law. -/
theorem stub_eq_mapped (bytes : Array U8 32#usize) : stub bytes = mapped bytes := by
  unfold stub mapped NFY_NBP_DigestDecode.decoded
  split_ifs <;> simp_all [canonical] <;> omega

theorem stub_source (bytes : Array U8 32#usize) :
    (do let r ← atomic_statement.decode_digest_canonical bytes
        ok (match r with
          | .Ok v => core.result.Result.Ok v
          | .Err _ => .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) = ok (stub bytes) := by
  rw [stub_eq_mapped]
  exact mapped_source bytes

#print axioms mapped_source
#print axioms stub_eq_mapped
#print axioms stub_source
end NJD_DigestLaw
end
