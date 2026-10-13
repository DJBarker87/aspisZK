import R1InputPair
import R1SpendSemantics

/-! The occupied slot is the same commitment carried by the input-note hash
block. The equality is derived from the path gates and literal copy links. -/
set_option autoImplicit false
namespace AspisR1.InputPairSelection
open R0P AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K]

open Classical in
theorem path_bit (A : Trace K) :
    (tracePath A 0).1 = if A 0 913 = 0 then false else true := by
  classical
  unfold tracePath
  change ((if A 0 913 = 0 then _ else _) : Bool × R0P.Digest K).1 = _
  split <;> rfl

theorem left_path (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (i : Fin 8) : (InputPair.leaf A).firstCommitment i = A (i.castAdd 21) 914 := by
  exact ((copy_path_cells_of_balance pub A hb 0).1 i).symm

theorem right_path (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (i : Fin 8) : (InputPair.leaf A).secondCommitment i = A ⟨8 + i.val, by omega⟩ 914 := by
  have h := (copy_path_cells_of_balance pub A hb 0).2.1 i
  change A ⟨i.val + 8, by omega⟩ 914 = A ⟨i.val + 8, by omega⟩ 64 +
    (if i.val = 7 then (1051521018 : K) else 0) at h
  simp only [Nat.add_comm i.val 8] at h
  exact (InputPairCopyLinks.right_cells pub A hb i).trans h.symm

theorem selected_output (pub : Public K) (A : Trace K)
    (hp : Holds pathFamily pub A) (hb : CopyLinkBalance pub A) :
    (InputPair.leaf A).selectedCommitment (tracePath A 0).1 = OutputNotes.output A 3 := by
  classical
  have hpath := (path_holds_iff pub A).mp hp 913 (pathBaseRow_mem 0)
  obtain ⟨_, _, _, _, _, _, _, _, hcurrent⟩ := copy_input_note_cells_of_balance pub A hb
  rw [path_bit]
  by_cases hz : A 0 913 = 0
  · rw [if_pos hz]
    change (InputPair.leaf A).firstCommitment = OutputNotes.output A 3
    funext i
    rw [left_path pub A hb i]
    have h := hpath.2.1 i
    rw [hz] at h
    have he : A (i.castAdd 21) 914 = A ⟨i.val + 1, by omega⟩ 913 := by
      rw [show succRow (913 : Fin 1024) = 914 by decide] at h
      simpa only [sub_zero, one_mul, sub_eq_zero, Fin.castAdd, Fin.castLE, Fin.addNat] using h
    exact he.trans (hcurrent i).symm
  · rw [if_neg hz]
    change (InputPair.leaf A).secondCommitment = OutputNotes.output A 3
    funext i
    rw [right_path pub A hb i]
    have h := hpath.2.2 i
    have he : A ⟨8 + i.val, by omega⟩ 914 = A ⟨i.val + 1, by omega⟩ 913 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hz)
    exact he.trans (hcurrent i).symm

structure Facts (pub : Public K) (A : Trace K) : Prop where
  valid : (InputPair.leaf A).Valid
  pair : OutputNotes.output A 4 =
    nodeCompress (InputPair.leaf A).firstCommitment (InputPair.leaf A).secondCommitment
  selected : (InputPair.leaf A).selectedCommitment (tracePath A 0).1 = OutputNotes.output A 3
  spendable : (InputPair.leaf A).SelectedSlotIsSpendable (tracePath A 0).1

theorem of_production (pub : Public K) (A : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) : Facts pub A := by
  exact ⟨InputPair.leaf_valid pub A h.1.2.1,
    InputPair.pair_output pub A h.1.2.2.2.1 h.1.2.2.2.2.2.2.1 h.2,
    selected_output pub A h.1.2.2.2.2.1 h.2,
    InputPair.selected_spendable pub A h.1.2.1 h.2⟩

#print axioms selected_output
#print axioms of_production
end AspisR1.InputPairSelection
