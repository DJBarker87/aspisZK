import AllAddressCollisionTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_TraceIndex
open FS FS2 FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem read_append (left right : List (I × A)) (a : I) :
    Read (left++right) a ↔ Read left a ∨ Read right a := by
  simp only [Read,List.map_append,List.mem_append]

theorem index_append (a : I) (left right : List (I × A)) :
    firstIdx a (left++right)=if Read left a then firstIdx a left else left.length+firstIdx a right := by
  induction left with
  | nil => simp [Read,firstIdx]
  | cons head tail ih =>
    obtain ⟨b,value⟩ := head
    by_cases same : b=a
    · subst b
      simp [firstIdx,Read]
    · simp only [List.cons_append,firstIdx,if_neg same,List.length_cons,ih,Read,List.map_cons,List.mem_cons]
      by_cases member : a∈tail.map Prod.fst
      · simp [member,Ne.symm same]
      · simp [member,Ne.symm same]
        omega

theorem index_append_of_read (a : I) (left right : List (I × A)) (read : Read left a) :
    firstIdx a (left++right)=firstIdx a left := by
  rw [index_append,if_pos read]

theorem before_append (left right : List (I × A)) (a b : I)
    (ha : Read left a) (hb : Read left b) (order : Before left a b) : Before (left++right) a b := by
  refine ⟨(read_append _ _ _).mpr (Or.inl ha),?_⟩
  rw [index_append_of_read _ _ _ ha,index_append_of_read _ _ _ hb]
  exact order.2

#print axioms read_append
#print axioms index_append
#print axioms index_append_of_read
#print axioms before_append
end AspisR1.PFin_TraceIndex
end
