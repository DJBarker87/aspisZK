import OraclePortFrozenOrderDecision

/-! Duplicate processing preserves every requested digest in the final live
frontier, and every requested leaf address is read before that frontier.
No equality of duplicate preimage bytes is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrder
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft
attribute [local instance] Classical.propDecidable

theorem leaves_retained (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind : Nat) (ps : List Nat) (rev live : Live)
    (success : (eval H (hashLeaves p q kind ps rev)).2 = some live) :
    (∀ e ∈ rev, e ∈ live) ∧
    (∀ pos ∈ ps, (index q kind pos,H (leaf p kind pos)) ∈ live ∧
      Read (eval H (hashLeaves p q kind ps rev)).1 (leaf p kind pos)) := by
  induction ps generalizing rev with
  | nil =>
    simp only [hashLeaves,eval,Option.some.injEq] at success
    subst live
    simp
  | cons pos rest ih =>
    cases rev with
    | nil =>
      simp only [hashLeaves,eval] at success ⊢
      obtain ⟨old,new⟩ := ih [(index q kind pos,H (leaf p kind pos))] success
      refine ⟨by simp,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨old _ (List.mem_cons_self ..),List.mem_cons_self ..⟩
      · have h := new x hx
        exact ⟨h.1,List.mem_cons_of_mem _ h.2⟩
    | cons entry tail =>
      rcases entry with ⟨j,v⟩
      by_cases eqi : index q kind pos = j
      · by_cases eqv : H (leaf p kind pos) = v
        · simp only [hashLeaves,eval,if_pos eqi,if_pos eqv] at success ⊢
          obtain ⟨old,new⟩ := ih ((j,v)::tail) success
          refine ⟨old,?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by rw [eqi,eqv]; exact old _ (List.mem_cons_self ..),List.mem_cons_self ..⟩
          · have h := new x hx
            exact ⟨h.1,List.mem_cons_of_mem _ h.2⟩
        · simp [hashLeaves,eval,eqi,eqv] at success
      · simp only [hashLeaves,eval,if_neg eqi] at success ⊢
        obtain ⟨old,new⟩ := ih ((index q kind pos,H (leaf p kind pos))::(j,v)::tail) success
        refine ⟨fun e he => old e (List.mem_cons_of_mem _ he),?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨old _ (List.mem_cons_self ..),List.mem_cons_self ..⟩
        · have h := new x hx
          exact ⟨h.1,List.mem_cons_of_mem _ h.2⟩

#print axioms leaves_retained
end AspisR1.OraclePortFrozenOrder
end
