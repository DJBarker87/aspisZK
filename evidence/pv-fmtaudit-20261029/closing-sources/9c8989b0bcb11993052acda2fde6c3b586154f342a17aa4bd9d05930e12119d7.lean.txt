import R1Z.PV_RDCD3_CB_MaskRootEq
import R1Z.PV_RDCD3_ArrayWrite194
import R1Z.PV_RDCD3_Cast194
import R1Z.PV_RDCD3_WordAll194
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_V217
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
/-- Fixed array repeat is a language primitive; this names its full storage
projection without reducing any concrete arithmetic structure. -/
theorem repeat_backing {T : Type} (n : Usize) (value : T) :
    (Array.repeat n value).val = List.replicate n.val value := rfl
/-- Complete source-shaped selected-mask Result, including failure/divergence.
Deployed Rust structural association is a separate checked evidence artifact;
compiler/memory/arithmetic primitive semantics remain the existing boundary. -/
theorem complete (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point =
      PV_RDCD3_CB_OwnedMask.owned.mask c1 mask g point :=
  (PV_RDCD3_CB_MaskRootEq.reference c1 mask g point).symm
/-- No success predicate or input domain hypothesis is introduced. -/
theorem carrier (P : Result Q → Prop) (c1 : Array Q 16#usize)
    (mask : Array Q 10#usize) (g : Q) (point : Array Q 10#usize) :
    P (PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point) ↔
      P (PV_RDCD3_CB_OwnedMask.owned.mask c1 mask g point) := by
  rw [complete]
#print axioms repeat_backing
#print axioms complete
#print axioms carrier
end R1Z.PV_RDCD3_V217
