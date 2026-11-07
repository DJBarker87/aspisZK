import NNH_Tx2ModelSlots
import NHJ_DistinctPacket
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctPort
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

/-- The exact seven-account source comparison, only in A2's successful
reference direction. No uniqueness of accounts or child success is assumed
independently: distinctKeys is read from that successful reference guard. -/
theorem seven (base : Ops) (env : RSL.Env)
 (a b c d e f g : r1_pool_adapter.owned.OwnedAccount)
 (distinct : RSL.distinctKeys ([a,b,c,d,e,f,g].map account)=true) :
 r1_pool_adapter.owned.require_distinct_accounts (NNH_Tx2ModelSlots.install base env)
  (Array.make 7#usize [a,b,c,d,e,f,g])=.ok (.Ok ()) := by
 have installed : NGL_ReadonlyModel.install (NNH_Tx2ModelSlots.install base env)=NNH_Tx2ModelSlots.install base env := rfl
 rw [←installed]
 rw [NHJ_DistinctPacket.seven]
 simp only [List.map_cons,List.map_nil,RSL.distinctKeys,List.all_cons,List.all_nil,
  Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,account] at distinct
 simp_all only [NND_Carrier.key_eq_iff,ne_eq]
 simp_all [NGL_DistinctInduction.reference,NGL_DistinctInduction.outer,
  NGL_DistinctInduction.inner,NGL_DistinctInduction.keyAt,Array.make,
  Usize.wrapping_add,bind_tc_ok]

#print axioms pairs
#print axioms indexed
#print axioms seven
end NNH_DistinctPort
