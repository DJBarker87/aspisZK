import R1ParsedStateCollision

/-! A parsed predecessor state obeys the same first-read order principle
as the older leading-state frame. The additional event is charged explicitly. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ParsedStateTrace
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem no_parsed_before (pred : Addr L → Option State) (Qtot : Nat)
    (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (ParsedStateCollision.bad pred Qtot) emptyTable tr)
    (a : Addr L) (ha : Read tr a) (b : Addr L) (hb : b = a ∨ Before tr b a) :
    pred b ≠ some (H a) := by
  intro heq
  have hbad : ¬ ParsedStateCollision.bad pred Qtot a
      (tableBefore emptyTable tr a) (H a) := by
    intro h
    exact hcoll (FS.hitsBad_of_first (ParsedStateCollision.bad pred Qtot)
      H a tr emptyTable hcons ha rfl h)
  apply hbad
  refine ⟨card_dom_lt H tr a hcons ha Qtot hQ, b, ?_, heq⟩
  rcases hb with he | hB
  · exact Or.inl he
  · right
    rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hB]
    exact Option.some_ne_none _

theorem parsed_after (pred : Addr L → Option State) (Qtot : Nat)
    (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (ParsedStateCollision.bad pred Qtot) emptyTable tr)
    (a b : Addr L) (ha : Read tr a) (hb : Read tr b) (hp : pred b = some (H a)) :
    Before tr a b := by
  have hne : b ≠ a := by
    intro he
    exact no_parsed_before pred Qtot H tr hcons hQ hcoll a ha b (Or.inl he) hp
  rcases before_total tr a b ha hb (Ne.symm hne) with h | h
  · exact h
  · exact (no_parsed_before pred Qtot H tr hcons hQ hcoll a ha b (Or.inr h) hp).elim

/-- The old event is preserved, and the parsed-state event is added. -/
def Coll {Pf : Type} (p : Params M Cv L) (pred : Addr L → Option State)
    (Qtot : Nat) (v : View (Addr L) State (Pf × Bool)) : Prop :=
  FS2.Duplex.Coll p Qtot v ∨
    hitsBad (ParsedStateCollision.bad pred Qtot) emptyTable v.1

theorem mass {X Pf : Type} (p : Params M Cv L) (pred : Addr L → Option State)
    (Qtot : Nat) (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State => indicator (Coll p pred Qtot
      (eval H (FS2.experiment P V x)))) ≤
      (Qtot : ℚ) * ((3 * Qtot : ℚ) / (256 ^ 32 : ℚ)) := by
  have hold := FS2.Duplex.coll_mass p Qtot P V x hQ
  have hnew := ParsedStateCollision.mass pred Qtot P V x hQ
  calc mean (fun H : Addr L → State => indicator (Coll p pred Qtot
          (eval H (FS2.experiment P V x))))
      ≤ mean (fun H : Addr L → State =>
          indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment P V x))) +
          indicator (hitsBad (ParsedStateCollision.bad pred Qtot) emptyTable
            (eval H (FS2.experiment P V x)).1)) := by
        apply mean_mono
        intro H
        exact indicator_or_le _ _
    _ = mean (fun H : Addr L → State =>
          indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment P V x)))) +
        mean (fun H : Addr L → State =>
          indicator (hitsBad (ParsedStateCollision.bad pred Qtot) emptyTable
            (eval H (FS2.experiment P V x)).1)) := mean_add _ _
    _ ≤ FS2.Duplex.κ Qtot + (Qtot : ℚ) * ((Qtot : ℚ) / (256 ^ 32 : ℚ)) :=
      add_le_add hold hnew
    _ = (Qtot : ℚ) * ((3 * Qtot : ℚ) / (256 ^ 32 : ℚ)) := by
      unfold FS2.Duplex.κ
      ring

#print axioms no_parsed_before
#print axioms parsed_after
#print axioms mass
end AspisR1.ParsedStateTrace
end
