import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S027
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 27: rust; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (pool : solana_pubkey.Pubkey)
 (slot : U64)
 (masterAccount : r1_pool_adapter.owned.OwnedAccount)
 (registryAccount : r1_pool_adapter.owned.OwnedAccount)
 (entryAccount : r1_pool_adapter.owned.OwnedAccount)
 (master : Box Master)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.registry verifier pool masterAccount master.payload registryAccount entryAccount slot)) next) ()) =
 tryThen (r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool masterAccount master.payload registryAccount entryAccount slot) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S027
end
