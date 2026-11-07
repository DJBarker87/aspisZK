import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S049
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 49: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (derivedLane : solana_pubkey.Pubkey)
 (laneKey : solana_pubkey.Pubkey)
 (next : Bool → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw (core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedLane laneKey)) next) ()) =
 ((core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedLane laneKey)) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 exact NMX_ResultSteps.raw ops owners _ next
#print axioms step
end NMX_S049
end
