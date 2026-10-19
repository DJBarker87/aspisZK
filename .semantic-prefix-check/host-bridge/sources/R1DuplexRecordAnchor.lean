import R1DuplexRecordPrefix

/-! Trace ordering and table cells when the endpoint is the final advance
read, without requiring a later endpoint read. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexRecordAnchor

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem before_anchor (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (init : Addr L) (hroot : s 0 = H init) (hi : Read tr init)
    (n : Nat) (hn : 0 < n)
    (habs : ∀ j < n,
      absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n,
      s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (c : Addr L)
    (hlast : Before tr (advanceA p (absorbed (n - 1))) c) :
    Before tr init c ∧
      (∀ j < n, Before tr
        (absorbA p (s j) (label j) (data j) (hD j)) c ∧
        Before tr (advanceA p (absorbed j)) c) := by
  let k := n - 1
  have hk : k + 1 = n := by dsimp [k]; omega
  have hklt : k < n := by omega
  have hlastAbs : Before tr
      (absorbA p (s k) (label k) (data k) (hD k))
      (advanceA p (absorbed k)) := by
    have hp : (advanceA p (absorbed k)).toBytes.take 32 =
        bytes (H (absorbA p (s k) (label k) (data k) (hD k))) := by
      rw [toBytes_advanceA, habs k hklt]
    exact noColl_prefix_after p Qtot H tr hcons hQ hcoll
      (absorbA p (s k) (label k) (data k) (hD k))
      (advanceA p (absorbed k)) (har k hklt) (hdr k hklt) hp
  have hprior := DuplexRecordPrefix.before_endpoint p H tr Qtot hcons hQ hcoll
    s absorbed label data hD init hroot hi k
    (fun j hj => habs j (by omega))
    (fun j hj => hstep j (by omega))
    (fun j hj => har j (by omega))
    (fun j hj => hdr j (by omega))
    (absorbA p (s k) (label k) (data k) (hD k))
    (har k hklt) (toBytes_absorbA p (s k) (label k) (data k) (hD k))
  have hlastChain := before_trans tr hlastAbs hlast
  refine ⟨before_trans tr hprior.1 hlastChain, ?_⟩
  intro j hj
  by_cases hjk : j = k
  · subst j
    exact ⟨hlastChain, hlast⟩
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
    (n : Nat) (hn : 0 < n)
    (habs : ∀ j < n,
      absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n,
      s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (c : Addr L)
    (hlast : Before tr (advanceA p (absorbed (n - 1))) c) :
    tableBefore emptyTable tr c init = some (s 0) ∧
      (∀ j < n, tableBefore emptyTable tr c
        (absorbA p (s j) (label j) (data j) (hD j)) = some (absorbed j) ∧
        tableBefore emptyTable tr c (advanceA p (absorbed j)) = some (s (j + 1))) := by
  have hbefore := before_anchor p H tr Qtot hcons hQ hcoll s absorbed label data
    hD init hroot hi n hn habs hstep har hdr c hlast
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

#print axioms before_anchor
#print axioms table_cells
end AspisR1.DuplexRecordAnchor
end
