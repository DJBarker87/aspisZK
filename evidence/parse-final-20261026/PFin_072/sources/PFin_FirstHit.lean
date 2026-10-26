import PFin_TraceIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_FirstHit
open FS FS2 FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem exists_first (bad : I → Table I A → A → Prop) (H : I → A)
    (tr : List (I × A)) (t : Table I A) (consistent : ∀ q∈tr,q.2=H q.1)
    (hit : hitsBad bad t tr) :
    ∃ a, Read tr a ∧ t a=none ∧ bad a (tableBefore t tr a) (H a) := by
  induction tr generalizing t with
  | nil => exact False.elim hit
  | cons head tail ih =>
    obtain ⟨i,value⟩ := head
    have atHead : value=H i := consistent _ (List.mem_cons_self ..)
    rcases hit with ⟨miss,badHead⟩ | rest
    · refine ⟨i,by simp [Read],miss,?_⟩
      simpa only [tableBefore,if_pos rfl,←atHead] using badHead
    · obtain ⟨a,read,miss,badRest⟩ := ih (put t i value)
        (fun q member=>consistent q (List.mem_cons_of_mem _ member)) rest
      have different : a≠i := by
        intro same
        subst a
        simp [put] at miss
      have oldMiss : t a=none := by simpa only [put,if_neg different] using miss
      refine ⟨a,by simp only [Read,List.map_cons,List.mem_cons];exact Or.inr read,oldMiss,?_⟩
      simpa only [tableBefore,if_neg (Ne.symm different)] using badRest

#print axioms exists_first
end AspisR1.PFin_FirstHit
end
