import R1DuplexPrefixTable

/-! Trace order and table cells for a sequence of absorb/advance records. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexRecordPrefix

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem before_endpoint (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (init : Addr L) (hroot : s 0 = H init) (hi : Read tr init)
    (n : Nat)
    (habs : ∀ j < n,
      absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n,
      s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (c : Addr L) (hc : Read tr c)
    (hp : c.toBytes.take 32 = bytes (s n)) :
    Before tr init c ∧
      (∀ j < n, Before tr
        (absorbA p (s j) (label j) (data j) (hD j)) c ∧
        Before tr (advanceA p (absorbed j)) c) := by
  induction n generalizing c with
  | zero =>
      have hprefix : c.toBytes.take 32 = bytes (H init) := by
        rw [← hroot]
        exact hp
      exact ⟨noColl_prefix_after p Qtot H tr hcons hQ hcoll init c hi hc hprefix,
        by intro j hj; omega⟩
  | succ n ih =>
      have hlast : Before tr (advanceA p (absorbed n)) c := by
        have hp' : c.toBytes.take 32 =
            bytes (H (advanceA p (absorbed n))) := by
          rw [← hstep n (by omega)]
          exact hp
        exact noColl_prefix_after p Qtot H tr hcons hQ hcoll
          (advanceA p (absorbed n)) c (hdr n (by omega)) hc hp'
      have hlastAbs : Before tr
          (absorbA p (s n) (label n) (data n) (hD n))
          (advanceA p (absorbed n)) := by
        have hp' : (advanceA p (absorbed n)).toBytes.take 32 =
            bytes (H (absorbA p (s n) (label n) (data n) (hD n))) := by
          rw [toBytes_advanceA, habs n (by omega)]
        exact noColl_prefix_after p Qtot H tr hcons hQ hcoll
          (absorbA p (s n) (label n) (data n) (hD n))
          (advanceA p (absorbed n)) (har n (by omega))
          (hdr n (by omega)) hp'
      have hlastChain := before_trans tr hlastAbs hlast
      have hprefixAbs :
          (absorbA p (s n) (label n) (data n) (hD n)).toBytes.take 32 = bytes (s n) :=
        toBytes_absorbA p (s n) (label n) (data n) (hD n)
      have hprior := ih (absorbA p (s n) (label n) (data n) (hD n))
        (fun j hj => habs j (by omega))
        (fun j hj => hstep j (by omega))
        (fun j hj => har j (by omega))
        (fun j hj => hdr j (by omega))
        (har n (by omega)) hprefixAbs
      refine ⟨before_trans tr hprior.1 hlastChain, ?_⟩
      intro j hj
      by_cases hlastj : j = n
      · subst j
        exact ⟨before_trans tr hlastAbs hlast, hlast⟩
      · have hbefore := hprior.2 j (by omega)
        exact ⟨before_trans tr hbefore.1 hlastChain,
          before_trans tr hbefore.2 hlastChain⟩

theorem table_cells (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (init : Addr L) (hroot : s 0 = H init) (hi : Read tr init)
    (n : Nat)
    (habs : ∀ j < n,
      absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n,
      s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (c : Addr L) (hc : Read tr c)
    (hp : c.toBytes.take 32 = bytes (s n)) :
    tableBefore emptyTable tr c init = some (s 0) ∧
      (∀ j < n, tableBefore emptyTable tr c
        (absorbA p (s j) (label j) (data j) (hD j)) = some (absorbed j) ∧
        tableBefore emptyTable tr c (advanceA p (absorbed j)) = some (s (j + 1))) := by
  have hbefore := before_endpoint p H tr Qtot hcons hQ hcoll s absorbed label data
    hD init hroot hi n habs hstep har hdr c hc hp
  constructor
  · rw [tableBefore_eq H tr emptyTable c init hcons, if_pos hbefore.1]
    exact congrArg some hroot.symm
  · intro j hj
    obtain ⟨habsBefore, hadvBefore⟩ := hbefore.2 j hj
    constructor
    · rw [tableBefore_eq H tr emptyTable c
        (absorbA p (s j) (label j) (data j) (hD j)) hcons, if_pos habsBefore]
      exact congrArg some (habs j hj).symm
    · rw [tableBefore_eq H tr emptyTable c (advanceA p (absorbed j)) hcons,
        if_pos hadvBefore]
      exact congrArg some (hstep j hj).symm

#print axioms before_endpoint
#print axioms table_cells
end AspisR1.DuplexRecordPrefix
end
