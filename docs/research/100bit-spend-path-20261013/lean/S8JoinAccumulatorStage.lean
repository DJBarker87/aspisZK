import S8JoinFinishField
import HchecksAccumulator
import R1LiteralOpeningView

/-! Exact S8 finalization/check stage at the ClosedSum used by dV_frozen.
The remaining S7 input is raw-field meaning at each reached column, not
callee success, phase bounds, canonicality, or a free S8 proposition. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinAccumulatorStage
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open S8OwnedP6ValueModel S8OwnedP6Finish S8JoinFinishField
open scoped BigOperators
attribute [local instance] Classical.propDecidable
abbrev Queries := Fin 22 → Fin 262144
abbrev Data := MatchingSupport.Data LiteralOpeningView.E

def weight (q : Queries) (rho : QM31Exact) (l : Fin 64) : QM31Exact :=
  ∑ j : Fin 22, rho^j.val * QueryResidualBridge.basis q j l

def fieldAt (out : Weights) (l : Fin 64) : QM31Exact :=
  ((out.val[l.val]?).map fieldValue).getD 0

def check (out : Weights) (data : Data) (q : Queries) (rho : QM31Exact) : Bool :=
  decide ((∑ l : Fin 64, data.f l * LiteralOpeningView.eK (fieldAt out l)) =
    ∑ j : Fin 22, (LiteralOpeningView.eK rho)^j.val * QueryResidualBridge.values data q j)

/-- The S8 execution and final Boolean are proved on rejecting arithmetic
inputs as well. Raw-field meaning is the exact S7 source representation join. -/
theorem finish_check (raw : Raw) (old : Weights) (data : Data) (q : Queries)
    (rho : QM31Exact) (size : old.length=64) (lengths : old.length≤raw.length)
    (meaning : ∀ (l : Fin 64) row, raw.val[l.val]?=some row → rawValue row=weight q rho l) :
    ∃ out : Weights, S8OwnedP6.finish_owned raw old=.ok out ∧
      check out data q rho = decide (HchecksAccumulator.ClosedSum LiteralOpeningView.eK data q rho) := by
  refine ⟨S8JoinFinishExact.output raw old,S8JoinFinishExact.reference_exact raw old lengths,?_⟩
  have cells (l : Fin 64) : fieldAt (S8JoinFinishExact.output raw old) l=weight q rho l := by
    have hi : l.val<old.length := by rw [size]; exact l.isLt
    have hr : l.val<raw.val.length := lt_of_lt_of_le hi lengths
    have row := meaning l raw.val[l.val] (List.getElem?_eq_getElem hr)
    simpa only [fieldAt,S8JoinFinishExact.output,List.getElem?_map,List.getElem?_take,
      if_pos hi,List.getElem?_eq_getElem hr,Option.map_some,Option.getD_some,
      modelValue_field] using row
  simp only [check,cells,HchecksAccumulator.ClosedSum,weight]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

#print axioms finish_check
end AspisR1.S8JoinAccumulatorStage
end
