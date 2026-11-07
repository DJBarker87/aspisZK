import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S004
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 4: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (next : r1_pool_adapter.owned.OwnedAccount → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 3#usize)) next) ()) =
 ((Slice.index_usize accounts 3#usize)) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 exact NMX_ResultSteps.raw ops owners _ next
#print axioms step
end NMX_S004
end
