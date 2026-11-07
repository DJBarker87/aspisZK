import NNH_Tx2ModelSlots
import NHJ_DistinctPacket
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctKeys
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem pairs (xs : List RSL.OwnedAccount) (h : RSL.distinctKeys xs=true) :
 xs.Pairwise (fun a b=>a.key≠b.key) := by
 induction xs with
 | nil => exact .nil
 | cons head tail ih =>
   simp only [RSL.distinctKeys,Bool.and_eq_true] at h
   apply List.pairwise_cons.mpr
   constructor
   · intro b member equal
     have diff := (List.all_eq_true.mp h.1) b member
     have ne : b.key≠head.key := of_decide_eq_true diff
     exact ne equal.symm
   · exact ih h.2

theorem indexed {A : Type} {R : A → A → Prop} (xs : List A) (h : xs.Pairwise R)
 (i j : Nat) (hi : i<xs.length) (hj : j<xs.length) (lt : i<j) :
 R xs[i] xs[j] := by
 induction xs generalizing i j with
 | nil => simp only [List.length_nil] at hi; omega
 | cons head tail ih =>
   obtain ⟨first,rest⟩:=List.pairwise_cons.mp h
   cases i with
   | zero =>
     cases j with
     | zero => omega
     | succ j => exact first _ (List.getElem_mem (by simpa using hj))
   | succ i =>
     cases j with
     | zero => omega
     | succ j => exact ih rest i j (by simpa using hi) (by simpa using hj) (by omega)


#print axioms pairs
#print axioms indexed
end NNH_DistinctKeys
