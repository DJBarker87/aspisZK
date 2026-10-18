import R1Z.GamesR1

set_option autoImplicit false
namespace R1Z.GamesR1
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS
  R0Z.FsAbortBounds R1Z.Batched R1Z.ModelsVR1 R1Z.LensR1 R1Z.TranscriptR1

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Any hit in a programmed list returns its recorded honest answer; a miss
falls back to the same shared oracle. This handles accepted transcript hits. -/
theorem lookup_honest_fallback {A V : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (H : A → V) (entries : List (A × V))
    (honest : ∀ e ∈ entries, e.2 = H e.1) (a : A) :
    (List.lookup a entries).getD (H a) = H a := by
  revert honest
  induction entries with
  | nil => intro; simp
  | cons e entries ih =>
      intro honest
      by_cases he : a = e.1
      · have hbeq : (a == e.1) = true := beq_iff_eq.mpr he
        simpa [List.lookup, hbeq, he] using honest e (by simp)
      · have hbeq : (a == e.1) = false := by
          cases h : (a == e.1) with
          | false => rfl
          | true =>
              have he' : a = e.1 := beq_iff_eq.mp h
              exact (he he').elim
        have htail : ∀ p ∈ entries, p.2 = H p.1 := by
          intro p hp
          exact honest p (by simp [hp])
        simp [List.lookup, hbeq, ih htail]

theorem progOracle_eq_shared_of_honestLog
    (W : R1Wire K CommitHandle Aux) (x : Statement K CommitHandle)
    (V : View K CommitHandle Aux R1Bat) (c : R1Coins W.Cm W.Tab) (tab : W.Tab)
    (honest : ∀ e ∈ verLog W x V c, e.2 = W.look tab e.1) (a : List UInt8) :
    progOracle W x V c tab a = W.look tab a := by
  unfold progOracle
  have hfallback := lookup_honest_fallback (W.look tab) (verLog W x V c) honest a
  cases hlookup : List.lookup a (verLog W x V c) with
  | none => simpa only [Option.getD, hlookup] using hfallback
  | some answer => simpa only [Option.getD, hlookup] using hfallback

#print axioms lookup_honest_fallback
#print axioms progOracle_eq_shared_of_honestLog
end R1Z.GamesR1
