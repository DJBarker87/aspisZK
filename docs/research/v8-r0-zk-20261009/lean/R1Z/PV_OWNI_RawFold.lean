import R1Z.PV_OWNI_Rows
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawFold
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def term (column : List Q) (sum : Q) (entry : Nat × Q) : Q :=
 valueAdd sum (valueMul entry.2 (column[entry.1]?.getD zero))

theorem term_result (column : List Q) (sum : Q) (entry : Nat × Q)
 (h:entry.1<column.length) :
 PV_RDB2D_SparseFold.term ops.toOps column sum entry=ok (term column sum entry) := by
 rw [PV_RDB2D_SparseFold.term,PV_RDB2D_SparseLookup.present column entry.1 h]
 simp only [bind_tc_ok,mul,add,term,List.getElem?_eq_getElem h,Option.getD_some]

theorem result (column : List Q) (xs : List (Nat × Q)) (sum : Q)
 (bound:∀ e∈xs,e.1<column.length) :
 PV_RDB2D_SparseFold.source ops.toOps column xs sum=ok (xs.foldl (term column) sum) := by
 induction xs generalizing sum with
 | nil => rfl
 | cons e es ih =>
  rw [PV_RDB2D_SparseFold.source,term_result column sum e (bound e (by simp))]
  simp only [bind_tc_ok,List.foldl_cons]
  exact ih _ (fun x hx=>bound x (by simp only [List.mem_cons];exact Or.inr hx))
#print axioms term_result
#print axioms result
end R1Z.PV_OWNI_RawFold
