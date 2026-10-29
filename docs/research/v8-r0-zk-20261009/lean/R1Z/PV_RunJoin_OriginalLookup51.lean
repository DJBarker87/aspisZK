import R1Z.GamesR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalLookup51

theorem lookup {A B : Type} [BEq A] [LawfulBEq A] (xs : List (A × B))
    (unique : (xs.map Prod.fst).Nodup) (a : A) (b : B) (mem : (a,b)∈xs) :
    xs.lookup a=some b := by
  induction xs with
  | nil => cases mem
  | cons head tail ih =>
    rcases head with ⟨x,y⟩
    have uniq : x∉tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup := by
      simpa only [List.map_cons,List.nodup_cons] using unique
    rw [List.lookup_cons]
    rcases List.mem_cons.mp mem with eq | mem
    · cases eq
      simp only [beq_self_eq_true,if_true]
    · have ne : a≠x := by
        intro eq
        apply uniq.1
        exact List.mem_map.mpr ⟨(a,b),mem,eq⟩
      rw [show (a==x)=false from beq_eq_false_iff_ne.mpr ne]
      exact ih uniq.2 mem
#print axioms lookup
end R1Z.PV_RunJoin_OriginalLookup51
