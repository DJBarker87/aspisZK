import NKI_LevelsComplete
import NJB_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelCarrier
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open NJX_AppendFold (State)
abbrev Pair := Array NQ 2#usize × Array NQ 2#usize

def pair (s : State) : Pair :=
 (NJB_ArrayCarrier.array (fun i => s ⟨i.val,by have h:=i.isLt;scalar_tac⟩),
  NJB_ArrayCarrier.array (fun i => s ⟨2+i.val,by have h:=i.isLt;scalar_tac⟩))
def state (p : Pair) : State :=
 ![NJB_ArrayCarrier.cell p.1 0,NJB_ArrayCarrier.cell p.1 1,
   NJB_ArrayCarrier.cell p.2 0,NJB_ArrayCarrier.cell p.2 1]

theorem state_pair (s : State) : state (pair s)=s := by
 funext j
 fin_cases j <;> simp [state,pair,NJB_ArrayCarrier.cell_array]

theorem pair_state (p : Pair) : pair (state p)=p := by
 apply Prod.ext
 · apply (congrArg NJB_ArrayCarrier.array ?_).trans (NJB_ArrayCarrier.array_cell p.1)
   funext i
   fin_cases i <;> simp [pair,state,NJB_ArrayCarrier.cell_array]
 · apply (congrArg NJB_ArrayCarrier.array ?_).trans (NJB_ArrayCarrier.array_cell p.2)
   funext i
   fin_cases i <;> simp [pair,state,NJB_ArrayCarrier.cell_array]

theorem injective (a b : Pair) (ha : ∀ j,Canon (state a j))
 (hb : ∀ j,Canon (state b j))
 (same : ∀ j,decode (state a j)=decode (state b j)) : a=b := by
 have eq : state a=state b := funext (fun j=>NJB_DecodeInjective.qm _ _ (ha j) (hb j) (same j))
 calc
  a=pair (state a):=(pair_state a).symm
  _=pair (state b):=congrArg pair eq
  _=b:=pair_state b

/-- Decoded equality is promoted to the complete literal pair only after
canonicality of all four returned cells has been proved on both sides. -/
theorem literal_result (a b : Pair) (ha : ∀ j,Canon (state a j))
 (hb : ∀ j,Canon (state b j))
 (same : ∀ j,decode (state a j)=decode (state b j)) :
 (ok a : Result Pair)=ok b := congrArg Result.ok (injective a b ha hb same)
#print axioms state_pair
#print axioms pair_state
#print axioms injective
#print axioms literal_result
end AspisR1.NKY_LevelCarrier
end
