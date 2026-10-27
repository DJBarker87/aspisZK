import R1Z.PV_Join_Wire_Op246
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry246
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op246Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), H → (Array Std.U8 32#usize) → (Array Std.U8 32#usize) → Result (Array
        Std.U8 32#usize) :=
  fun {H} inst hash left right => PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op246 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext H inst hash left right
  exact R1Z.PV_Join_Wire_Op246.op246_source base ops inst hash left right
#print axioms equation
end R1Z.PV_Join_Wire_Entry246
