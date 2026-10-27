import RPv_FIx_ScheduleModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_InitialShape
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIx_ScheduleModel (Variant Openings)
open FIx_HighSumInner (Selectors)
theorem value (v : Variant) (s : Selectors) (o : Openings) (j : Fin (16#usize).val) :
    FIx_ScheduleModel.initial v s o j =
      if j.val=9 then FIx_ScheduleModel.initialRaw v s o j-FIx_ScheduleModel.low s 0*FIx_ScheduleModel.length v s
      else if j.val=8 then FIx_ScheduleModel.initialRaw v s o j-FIx_ScheduleModel.low s 0*FIx_ScheduleModel.domain v s
      else FIx_ScheduleModel.initialRaw v s o j := by
  by_cases h9 : j.val=9
  · have eq : j=(⟨9,by decide⟩ : Fin (16#usize).val) := Fin.ext h9
    subst j
    rw [FIx_ScheduleModel.initial,Function.update_self,if_pos rfl]
  · have ne9 : j≠(⟨9,by decide⟩ : Fin (16#usize).val) := fun h=>h9 (congrArg Fin.val h)
    rw [FIx_ScheduleModel.initial,Function.update_of_ne ne9,if_neg h9]
    by_cases h8 : j.val=8
    · have eq : j=(⟨8,by decide⟩ : Fin (16#usize).val) := Fin.ext h8
      subst j
      rw [Function.update_self,if_pos rfl]
    · have ne8 : j≠(⟨8,by decide⟩ : Fin (16#usize).val) := fun h=>h8 (congrArg Fin.val h)
      rw [Function.update_of_ne ne8,if_neg h8]
#print axioms value
end AspisR1.FIz_InitialShape
end
