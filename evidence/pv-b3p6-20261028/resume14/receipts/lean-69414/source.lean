import PV_B3P_SliceLoop13227
import PV_B3P_D188Link14227
namespace PV_B3P_Groups14227
open Aeneas Aeneas.Std PV_B3P_Binding13227
set_option autoImplicit false
abbrev Four14 := Array Q14 4#usize
abbrev SliceFn14 := (Four14 → Usize → Result Four14) → Four14 → Result Four14

def PV_B3P_Link_slice14 (native : SliceFn14) : Prop :=
  ∀ step state, native step state = PV_B3P_Binding9227.usize_plan step 4 0#usize state
/-- A typed family, indexed by the complete source-cone catalogue. At a native
instantiation, Sig and model must be the pinned declarations' actual signatures
and models. This predicate supplies no omission/unreachability certificate. -/
def PV_B3P_Link_std_dependency_closure14 {ι : Type} (Sig : ι → Type)
    (native model : (i : ι) → Sig i) : Prop := ∀ i, native i = model i

theorem slice_model_binding14 : PV_B3P_Link_slice14 (@slice_loop13 Four14) :=
  slice_loop_four13

theorem std_model_witness14 {ι : Type} (Sig : ι → Type) (model : (i : ι) → Sig i) :
    ∃ native, PV_B3P_Link_std_dependency_closure14 Sig native model :=
  ⟨model,fun _ => rfl⟩
#print axioms slice_model_binding14
#print axioms std_model_witness14
end PV_B3P_Groups14227
