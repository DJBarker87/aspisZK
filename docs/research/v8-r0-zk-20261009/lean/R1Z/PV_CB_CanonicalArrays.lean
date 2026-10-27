import R1Z.PV_CB_CanonicalTower
import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalArrays
open Aeneas Aeneas.Std Result

def Valid {A : Type} {n : Usize} (predicate : A → Prop) (values : Array A n) : Prop :=
  ∀ value ∈ values.val, predicate value

theorem read {A : Type} {n : Usize} (predicate : A → Prop) (values : Array A n)
    (valid : Valid predicate values) (i : Usize) (bound : i.val < n.val) :
    ∃ value, Array.index_usize values i = ok value ∧ predicate value := by
  have inside : i.val < values.val.length := by rw [values.property]; exact bound
  refine ⟨values.val[i.val],?_,valid _ (List.getElem_mem inside)⟩
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem inside]

theorem repeat_valid {A : Type} (predicate : A → Prop) (n : Usize) (value : A)
    (valid : predicate value) : Valid predicate (Array.repeat n value) := by
  intro element member
  have same : element = value := by
    simp only [Array.repeat,List.mem_replicate] at member
    exact member.2
  simpa only [same] using valid
#print axioms read
#print axioms repeat_valid
end R1Z.PV_CB_CanonicalArrays
