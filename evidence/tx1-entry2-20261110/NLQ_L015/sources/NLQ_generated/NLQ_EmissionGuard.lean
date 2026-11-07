import NGL_ArrayEquality
import NLD_Stage1Source
import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NLQ_EmissionGuard
open Aeneas Aeneas.Std Result AspisR1
/-- Install only the documented U8 equality primitive. No child reply is
chosen or assumed; on eleven the emitted definition never enters any child. -/
def equality (ops : AdapterRw.Ops) : AdapterRw.Ops :=
 {ops with op1 := fun _ d a => Hiq_DispatchSource.eqU8 d a}
theorem eleven_rejected (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) :
 AdapterRw.r1_pool_adapter.owned.stage1_owned (equality ops) program accounts NJD_Prefixes.eleven =
 .ok (.Err .InvalidInstructionData) := by
 simp only [AdapterRw.r1_pool_adapter.owned.stage1_owned,equality]
 simp [Hiq_DispatchSource.eqU8,NJD_Prefixes.eleven,Array.make]
/-- NLD's proven erasure inherits the same guard restriction. This theorem
records the mismatch; it is not an implementation bridge. -/
theorem nld_eleven_rejected (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) :
 (NLD_Stage1Source.stage1Owned (equality ops) program accounts NJD_Prefixes.eleven).2 =
 .ok (.Err .InvalidInstructionData) := by
 rw [NLD_Stage1Source.erasure]
 exact eleven_rejected ops program accounts
#print eleven_rejected
#print axioms eleven_rejected
#print axioms nld_eleven_rejected
end NLQ_EmissionGuard
