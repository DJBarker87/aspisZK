import R1Z.PV_RunJoin_SamplerDigitsField50
import R1Z.PV_RunJoin_DigitsValue50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerDigitRank50
open Aeneas Aeneas.Std
open ProverCommitWideOps48
open PV_B2_C_ArrayDigits (limb)
open PV_RunJoin_SamplerDigitsField50 (digits)
open AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge (values)
open scoped BigOperators

theorem values_ofFn (a : Array U32 8#usize) :
    values a=List.ofFn (fun i : Fin 8 => (limb a i).val) := by
  apply List.ext_getElem
  · simp only [values,List.length_map,a.property,List.length_ofFn]
    rfl
  · intro i hi hk
    simp only [values,List.getElem_map,List.getElem_ofFn,limb]

theorem rank (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a) :
    (AspisR1.SamplerRanking.digitsRank AspisCircleGroupOrder.P 8 (digits a h)).val=
      AspisR1.SamplerAddDigits.digitsValue AspisCircleGroupOrder.P (values a) := by
  rw [AspisR1.SamplerRanking.digitsRank_value,values_ofFn,PV_RunJoin_DigitsValue50.complete]
  rfl

theorem complete (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a) :
    value (PV_RunJoin_SamplerRaw49.raw a)=R0C.ModuloField.fieldRank
      (AspisR1.SamplerRanking.digitsRank AspisCircleGroupOrder.P 8 (digits a h)) := by
  rw [PV_RunJoin_SamplerDigitsField50.complete]
  change R0C.ModuloField.digitsField (digits a h)=
    R0C.ModuloField.digitsField ((finFunctionFinEquiv : (Fin 8 → Fin AspisCircleGroupOrder.P) ≃
      Fin (AspisCircleGroupOrder.P^8)).symm (finFunctionFinEquiv (digits a h)))
  rw [Equiv.symm_apply_apply]

theorem value_at (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a)
    (n : Nat) (bound : n<AspisCircleGroupOrder.P^8)
    (hn : AspisR1.SamplerAddDigits.digitsValue AspisCircleGroupOrder.P (values a)=n) :
    value (PV_RunJoin_SamplerRaw49.raw a)=R0C.ModuloField.fieldRank ⟨n,bound⟩ := by
  have eq : AspisR1.SamplerRanking.digitsRank AspisCircleGroupOrder.P 8 (digits a h)=⟨n,bound⟩ :=
    Fin.ext ((rank a h).trans hn)
  rw [←eq]
  exact complete a h
#print axioms values_ofFn
#print axioms rank
#print axioms complete
#print axioms value_at
end R1Z.PV_RunJoin_SamplerDigitRank50
