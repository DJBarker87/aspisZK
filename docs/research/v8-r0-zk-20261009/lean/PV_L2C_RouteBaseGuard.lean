import PV_L2C_ClientRoute
import PV_L2C_MaskRange
import PV_L2C_BaseGuard
set_option autoImplicit false
noncomputable section
namespace PV_L2C_RouteBaseGuard
open Aeneas Aeneas.Std Result R1Z

def column (bank : PV_L2C_MaskRange.Bank) (c : Fin 16) : List U32 :=
  List.ofFn (fun r : Fin 1024 => (⟨bank c r⟩ : U32))

theorem bank_expected (bank : PV_L2C_MaskRange.Bank) (hc : PV_L2C_MaskRange.Canonical bank)
    (c : Fin 16) : PV_L2C_BaseGuard.check (column bank c) = .ok () := by
  apply PV_L2C_BaseGuard.expected
  · simp only [column,List.length_ofFn]
  · intro j hj
    rw [column,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hj]
    exact hc c ⟨j,hj⟩
#print axioms bank_expected

def bank (columns : PV_Src_ForestTrace.Columns) : PV_L2C_MaskRange.Bank :=
  fun c r => (PV_Src_Forest_Columns.read columns ⟨c.val,by omega⟩ r).bv

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
include K in
theorem transfer_bank (t : PV_L2C_ClientRoute.Transfer) :
    PV_L2C_MaskRange.Canonical (bank t.compiled.semantic_c1.c1) := by
  intro c r
  exact (PV_L2C_ClientRoute.transfer_columns (K:=K) t).2 ⟨c.val,by omega⟩ r
#print axioms transfer_bank

include K in
theorem withdrawal_bank (t : PV_L2C_ClientRoute.Withdrawal) :
    PV_L2C_MaskRange.Canonical (bank t.compiled.semantic_c1.c1) := by
  intro c r
  exact (PV_L2C_ClientRoute.withdrawal_columns (K:=K) t).2 ⟨c.val,by omega⟩ r
#print axioms withdrawal_bank

include K in
theorem transfer_masked (t : PV_L2C_ClientRoute.Transfer)
    (cells : List (PV_L2C_MaskRange.Cell × PV_L2C_M31.word))
    (hm : ∀ cm ∈ cells, PV_L2C_M31.canonical cm.2)
    (active : Fin 1024 → Bool) (dependent : Fin 16 → Usize) (c : Fin 16) :
    PV_L2C_BaseGuard.check (column
      (PV_L2C_MaskRange.balance (PV_L2C_MaskRange.applyCells
        (bank t.compiled.semantic_c1.c1) cells) active dependent) c) = .ok () :=
  bank_expected _ (PV_L2C_MaskRange.application _ (transfer_bank (K:=K) t) cells hm active dependent) c
#print axioms transfer_masked

include K in
theorem withdrawal_masked (t : PV_L2C_ClientRoute.Withdrawal)
    (cells : List (PV_L2C_MaskRange.Cell × PV_L2C_M31.word))
    (hm : ∀ cm ∈ cells, PV_L2C_M31.canonical cm.2)
    (active : Fin 1024 → Bool) (dependent : Fin 16 → Usize) (c : Fin 16) :
    PV_L2C_BaseGuard.check (column
      (PV_L2C_MaskRange.balance (PV_L2C_MaskRange.applyCells
        (bank t.compiled.semantic_c1.c1) cells) active dependent) c) = .ok () :=
  bank_expected _ (PV_L2C_MaskRange.application _ (withdrawal_bank (K:=K) t) cells hm active dependent) c
#print axioms withdrawal_masked
end PV_L2C_RouteBaseGuard
