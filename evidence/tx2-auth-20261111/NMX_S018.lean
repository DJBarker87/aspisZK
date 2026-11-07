import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S018
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 18: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (pool : solana_pubkey.Pubkey)
 (masterKeyBytes : Array U8 32#usize)
 (master : Box Master)
 (next : Bool → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  master.payload.identity.pool masterKeyBytes)) next) ()) =
 ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  master.payload.identity.pool masterKeyBytes)) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 exact NMX_ResultSteps.raw ops owners _ next
#print axioms step
end NMX_S018
end
