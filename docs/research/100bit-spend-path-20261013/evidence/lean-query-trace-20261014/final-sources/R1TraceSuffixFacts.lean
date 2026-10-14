import R0C.V3.DQDecodes

/-! Consistency and read facts for a transcript suffix beginning at a read. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.TraceSuffix

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {I A : Type} [DecidableEq I]

theorem traceFrom_consistent (H : I → A) (tr : List (I × A)) (a : I)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (haRead : Read tr a) :
    ∀ q ∈ FS2.traceFrom tr a, q.2 = H q.1 := by
  obtain ⟨rest, htrace, hrest, _⟩ :=
    FS2.Duplex.traceFrom_eq H tr a hcons haRead
  intro q hq
  rw [htrace] at hq
  rcases List.mem_cons.mp hq with hhead | htail
  · have hfirst : q.1 = a := congrArg Prod.fst hhead
    simpa [hfirst] using congrArg Prod.snd hhead
  · exact hrest q htail

theorem absent_read (H : I → A) (tr : List (I × A)) (a b : I)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (haRead : Read tr a) (hbRead : Read tr b)
    (hnone : tableBefore emptyTable tr a b = none) :
    Read (FS2.traceFrom tr a) b := by
  by_cases hba : b = a
  · subst b
    exact R0C.V3.DQ.read_traceFrom a a tr haRead haRead (Or.inl rfl)
  · rcases before_total tr a b haRead hbRead (Ne.symm hba) with hab | hba'
    · exact R0C.V3.DQ.read_traceFrom a b tr haRead hbRead (Or.inr hab)
    · have hsome : tableBefore emptyTable tr a b = some (H b) := by
        rw [FS2.Duplex.tableBefore_eq H tr emptyTable a b hcons, if_pos hba']
      rw [hsome] at hnone
      cases hnone

theorem after_absent (H : I → A) (tr : List (I × A)) (a b : I)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hab : Before tr a b) :
    tableBefore emptyTable tr a b = none := by
  rw [FS2.Duplex.tableBefore_eq H tr emptyTable a b hcons]
  have hnot : ¬ Before tr b a := by
    intro hba
    exact FS2.Duplex.before_irrefl tr a (FS2.Duplex.before_trans tr hab hba)
  simp [hnot, emptyTable]

#print axioms traceFrom_consistent
#print axioms absent_read
#print axioms after_absent

end AspisR1.TraceSuffix
end
