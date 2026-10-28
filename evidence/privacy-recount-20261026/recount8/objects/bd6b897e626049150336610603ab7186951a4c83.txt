import R0P.PositivityChain
import R0P.Occupancy
import R0P.Digest

/-! The change-sentinel obstruction (t2b2b/DESIGN-BUILDER-MODEL.txt §5).

For a private transfer, any trace satisfying the occupancy and digest
families together with CopyLinkBalance has `pub.change 7 ≠ 0`: copy link
1124073492 (CopyConstants.lean, transfer-only) copies the change digest
(row 523, columns 0..7) into the output occupancy row 1018 (columns 2..9),
whose sentinel equation `A 9 · A 1 − A 0 = 0` with `A 0 = 1` forces
`A 9 ≠ 0`.  The Rust builder enforces the same condition by aborting
(two_outputs, pair_tree_profile.rs:206-226: "a zero sentinel is a retry
condition for note-salt generation").  Rspend (SpendRelation.lean:41) does not
contain it, so no builder can satisfy `BuilderRefines S Rspend` on transfer
witnesses whose change commitment has a zero last limb. -/
set_option autoImplicit false
namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

/-- COPY_LINKS entry 1124073492 (CopyConstants.lean, the third entry of
`copyLinksAfterPositivity`). -/
def changeOccLink : CopyLink := ⟨1124073492, 1, 0, ⟨523, 0, 1⟩, ⟨1018, 0, 11⟩⟩

theorem changeOccLink_mem : changeOccLink ∈ copyLinks :=
  List.mem_append_right _
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

theorem change_occ_cell (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (hv : pub.variant = .privateTransfer) : A 7 523 = A 9 1018 := by
  have hw : copyLinkWeight (K := K) changeOccLink pub.nextPairIndex pub.variant ≠ 0 := by
    show (if pub.variant = .privateTransfer then (1 : K) else 0) ≠ 0
    rw [if_pos hv]
    exact one_ne_zero
  have h := hb changeOccLink changeOccLink_mem hw
  have h7 := congrFun (congrArg Prod.snd h) 7
  have h7' : A 7 523 + ((0 : Nat) : K) = A 9 1018 + ((0 : Nat) : K) := h7
  simpa using h7'

theorem change_sentinel_of_balance (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) (hd : Holds digestFamily pub A)
    (hb : CopyLinkBalance pub A) (hv : pub.variant = .privateTransfer) : pub.change 7 ≠ 0 := by
  have ho' := (occupancy_holds_iff pub A).1 ho
  have hd' := (digest_holds_iff pub A).1 hd
  have hs : A 9 1018 * A 1 1018 - A 0 1018 = 0 := (ho'.1 1018 (Or.inr rfl)).2.1
  have h0 : A 0 1018 = 1 := by
    have := ho'.2.2
    rw [hv] at this
    exact this
  have hc : A 7 523 = pub.change 7 := hd'.2.2.2.1 7
  intro hz
  rw [← change_occ_cell pub A hb hv, hc, hz, h0, zero_mul, zero_sub, neg_eq_zero] at hs
  exact one_ne_zero hs

#print axioms changeOccLink_mem
#print axioms change_occ_cell
#print axioms change_sentinel_of_balance
end R0Z.BuilderModel
