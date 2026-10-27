import PV_B1_Install
set_option autoImplicit false
noncomputable section
namespace PV_B1_ReferenceInstall
open Aeneas Aeneas.Std Result PV_B1_Host PV_B1_Install PV_B1_Transport
variable [ExternalTypes]

def helper (xs : Slice HQ) : Result (Option HQ) :=
  ok (Option.map PV_B1_Carrier230.fromQ (PV_B1_SumOriginal.original_row (sliceMap PV_B1_Carrier230.toQ xs)))

def powers (N : Usize) (x : HW) : Result (Array HW N) :=
  resultMap (arrayMap PV_B1_CarrierWide.fromW)
    (PV_B1_PowersOriginal.weights.powers N (PV_B1_CarrierWide.toW x))

def pole (values : Rows) (masks : Array U16 64#usize) (chi : HQ) : Result Bool :=
  PV_B1_PoleOriginal.reference.all_slots_clear (PV_B1_Install.rows values) masks (PV_B1_Carrier258.toQ chi)

def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op230:=helper,op254:=powers,op258:=pole}

theorem source_eq (ops : ExternalFuns) : PV_B1_Install.selected ops=selected ops := by
  have h230 : PV_B1_Install.helper=helper := by
    funext xs
    exact PV_B1_Install.op230_source ops xs
  have h254 : PV_B1_Install.powers=powers := by
    funext N x
    exact PV_B1_Install.op254_source ops N x
  have h258 : PV_B1_Install.pole=pole := by
    funext values masks chi
    exact PV_B1_Install.op258_source ops values masks chi
  unfold PV_B1_Install.selected selected
  rw [h230,h254,h258]

-- Equality in a typed value/Result context; no native observer claim.
theorem context_result {A : Type} (context : ExternalFuns → Result A) (ops : ExternalFuns) :
    context (PV_B1_Install.selected ops)=context (selected ops) := congrArg context (source_eq ops)
#print axioms source_eq
#print axioms context_result
end PV_B1_ReferenceInstall
