import NHY_NaturalReads
import NIS_EntryStatus
set_option autoImplicit false
noncomputable section
namespace NIJ_EntryRecord
open Aeneas Aeneas.Std Result
abbrev Entry := NCX_Reference.VerifierRegistryEntryV2

def record (b : Slice U8) (len : b.val.length=320)
 (status : NCX_Reference.VerifierEntryStatusV1) : Entry := {
 status:=status
 pool:=NHY_NaturalReads.array b 8 32#usize (by change 8+32 ≤ b.val.length;omega)
 verifier_program:=NHY_NaturalReads.array b 40 32#usize (by change 40+32 ≤ b.val.length;omega)
 profile_binding:=NHY_NaturalReads.array b 72 32#usize (by change 72+32 ≤ b.val.length;omega)
 release_binding:=NHY_NaturalReads.array b 104 32#usize (by change 104+32 ≤ b.val.length;omega)
 loader_program:=NHY_NaturalReads.array b 136 32#usize (by change 136+32 ≤ b.val.length;omega)
 programdata_address:=NHY_NaturalReads.array b 168 32#usize (by change 168+32 ≤ b.val.length;omega)
 executable_hash:=NHY_NaturalReads.array b 200 32#usize (by change 200+32 ≤ b.val.length;omega)
 expected_upgrade_authority:=NHY_NaturalReads.array b 232 32#usize (by change 232+32 ≤ b.val.length;omega)
 policy_binding:=NHY_NaturalReads.array b 280 32#usize (by change 280+32 ≤ b.val.length;omega)
 activation_slot:=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 264 8#usize (by change 264+8 ≤ b.val.length;omega))
 retirement_slot:=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 272 8#usize (by change 272+8 ≤ b.val.length;omega))
 statement_version:=NHY_ZeroStep.byte b 6
 bump:=NHY_ZeroStep.byte b 312
 programdata_bump:=NHY_ZeroStep.byte b 313
}
theorem domain (b : Slice U8) (len : b.val.length=320) (o count : Nat)
 (inside : o+count ≤ 320) : o+count ≤ b.val.length := by omega

/-- All native status-error constructors select the sole semantic error. -/
theorem status_error (v : U8) (err : NIJ_EntryStatus.Err)
 (h : NIJ_EntryStatus.value v=.Err err) : err=.InvalidStatus := by
 unfold NIJ_EntryStatus.value at h
 split at h <;> cases h <;> rfl
#print axioms domain
#print axioms status_error
end NIJ_EntryRecord
