import R1OutputCopyLinks
import R0P.Semantics
import R0P.Asset

/-! Output-note extraction from the existing production families. The block
composition follows R0P.Extraction's input-note proof, keeping the permutation
opaque. Recipient extraction is explicitly private-transfer-only and public
recipient binding additionally requires the matching Option to be present.
No ownership of either output key or append transition is asserted here. -/
set_option autoImplicit false
namespace AspisR1.OutputNotes
open R0P
variable {K : Type} [Field K]

attribute [local irreducible] poseidonPermutation

def chunk (A : Trace K) (block : Fin 57) : Digest K :=
  digestOf (poseidonState A block 12)

def output (A : Trace K) (block : Fin 57) : Digest K :=
  digestOf (poseidonState A block 11)

/-- The six salt limbs in the middle chunk, then two in the final chunk. -/
def salt (A : Trace K) (middle last : Fin 57) : Digest K := fun i =>
  if h : i.val < 6 then chunk A middle ⟨i.val + 2, by omega⟩
  else chunk A last ⟨i.val - 6, by omega⟩

theorem block_step (pub : Public K) (A : Trace K)
    (hpo : Holds poseidonScalarFamily pub A) (block : Fin 57) :
    poseidonState A block 11 = spongeStep (poseidonState A block 0) (chunk A block) := by
  rw [poseidon_scalar_holds_output pub A hpo block]
  unfold spongeStep
  apply congrArg poseidonPermutation
  funext lane
  simp only [poseidonAbsorbedInput, absorb, chunk, digestOf, poseidonState]
  split_ifs <;> rfl

theorem initial (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (block : Fin 57)
    (hf : ScheduleFull pub.variant block.val) :
    poseidonState A block 0 = scheduleTarget pub.variant block.val := by
  have hdiv : (poseidonBlockRow block 0).val / 16 = block.val := by
    change (16 * block.val + 0) / 16 = block.val
    omega
  have hmod : (poseidonBlockRow block 0).val % 16 = 0 := by
    change (16 * block.val + 0) % 16 = 0
    omega
  funext lane
  have hh := ((schedule_holds_iff pub A).mp hs).1 _ hmod (by rwa [hdiv]) lane
  simpa only [hdiv] using hh

theorem last_padding (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (block : Fin 57)
    (hb : block.val = 29 ∨ block.val = 32) (i : Fin 8) (hi : 2 ≤ i.val) :
    chunk A block i = 0 := by
  have hdiv : (poseidonBlockRow block 12).val / 16 = block.val := by
    change (16 * block.val + 12) / 16 = block.val
    omega
  have hmod : (poseidonBlockRow block 12).val % 16 = 12 := by
    change (16 * block.val + 12) % 16 = 12
    omega
  have hz := (schedule_holds_iff pub A).mp hs |>.2.2
    (poseidonBlockRow block 12) hmod (i.castAdd 8) (by
      rw [hdiv]
      change ScheduleAbsorbs pub.variant block.val i.val
      simp only [ScheduleAbsorbs, if_neg (show ¬ i.val < 2 from by omega),
        if_pos i.isLt]
      rcases hb with hb | hb
      · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inl hb))
  exact hz

theorem middle_chunk (A : Trace K) (middle last : Fin 57) (value asset : K)
    (hv : chunk A middle 0 = value) (ha : chunk A middle 1 = asset) :
    chunk A middle = fun i : Fin 8 =>
      if i.val = 0 then value else if i.val = 1 then asset
      else salt A middle last ⟨i.val - 2, by omega⟩ := by
  funext i
  by_cases h0 : i.val = 0
  · rw [if_pos h0]
    have he : i = 0 := Fin.ext h0
    subst i
    exact hv
  · rw [if_neg h0]
    by_cases h1 : i.val = 1
    · rw [if_pos h1]
      have he : i = 1 := Fin.ext h1
      subst i
      exact ha
    · rw [if_neg h1]
      unfold salt
      rw [dif_pos (by omega : i.val - 2 < 6)]
      exact congrArg (chunk A middle) (Fin.ext (by
        change i.val = i.val - 2 + 2
        omega))

theorem last_chunk (A : Trace K) (middle last : Fin 57)
    (hz : ∀ i : Fin 8, 2 ≤ i.val → chunk A last i = 0) :
    chunk A last = fun i : Fin 8 =>
      if h : i.val < 2 then salt A middle last ⟨i.val + 6, by omega⟩ else 0 := by
  funext i
  by_cases hi : i.val < 2
  · rw [dif_pos hi]
    unfold salt
    rw [dif_neg (by omega : ¬ i.val + 6 < 6)]
    exact congrArg (chunk A last) (Fin.ext (by
      change i.val = i.val + 6 - 6
      omega))
  · rw [dif_neg hi]
    exact hz i (by omega)

/-- A symbolic three-block hash composition; it does not evaluate Poseidon. -/
theorem note_of_blocks (pub : Public K) (A : Trace K)
    (hpo : Holds poseidonScalarFamily pub A) (first middle last : Fin 57)
    (value asset : K)
    (hinit : poseidonState A first 0 = spongeInit 0x4153_0003 18)
    (h01 : poseidonState A middle 0 = poseidonState A first 11)
    (h12 : poseidonState A last 0 = poseidonState A middle 11)
    (hv : chunk A middle 0 = value) (ha : chunk A middle 1 = asset)
    (hz : ∀ i : Fin 8, 2 ≤ i.val → chunk A last i = 0) :
    output A last = noteCommitment (chunk A first) value asset (salt A middle last) := by
  unfold noteCommitment output
  rw [block_step pub A hpo last, h12, block_step pub A hpo middle,
    h01, block_step pub A hpo first, hinit,
    middle_chunk A middle last value asset hv ha, last_chunk A middle last hz]

theorem change_hash (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (ha : Holds assetFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) :
    output A 32 = noteCommitment (chunk A 30) (A 10 1012) pub.assetId (salt A 31 32) := by
  obtain ⟨hc01, hc12, hv⟩ := OutputCopyLinks.change_cells pub A hb
  apply note_of_blocks pub A hpo 30 31 32
  · rw [initial pub A hs 30 (by right; right; right; left; rfl)]
    funext lane
    simp [scheduleTarget, spongeInit]
  · funext lane; exact (hc01 lane).symm
  · funext lane; exact (hc12 lane).symm
  · exact hv
  · exact (asset_holds_iff pub A).mp ha |>.2.1
  · exact last_padding pub A hs 32 (Or.inr rfl)

theorem recipient_hash (pub : Public K) (A : Trace K)
    (hvariant : pub.variant = .privateTransfer)
    (hs : Holds scheduleFamily pub A) (ha : Holds assetFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) :
    output A 29 = noteCommitment (chunk A 27) (A 10 1010) pub.assetId (salt A 28 29) := by
  obtain ⟨hc01, hc12, hv⟩ := OutputCopyLinks.recipient_cells pub A hb hvariant
  apply note_of_blocks pub A hpo 27 28 29
  · rw [initial pub A hs 27 (by right; right; right; right; left; rfl)]
    funext lane
    simp [scheduleTarget, spongeInit, hvariant]
  · funext lane; exact (hc01 lane).symm
  · funext lane; exact (hc12 lane).symm
  · exact hv
  · exact (asset_holds_iff pub A).mp ha |>.2.2.1 hvariant
  · exact last_padding pub A hs 29 (Or.inl rfl)

theorem change_public (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (ha : Holds assetFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    pub.change = noteCommitment (chunk A 30) (A 10 1012) pub.assetId (salt A 31 32) := by
  have hbind : pub.change = output A 32 := by
    funext i
    exact ((digest_holds_iff pub A).mp hd |>.2.2.2.1 i).symm
  exact hbind.trans (change_hash pub A hs ha hpo hb)

theorem recipient_public (pub : Public K) (A : Trace K)
    (hvariant : pub.variant = .privateTransfer) (recipient : Digest K)
    (hpresent : pub.recipient = some recipient)
    (hs : Holds scheduleFamily pub A) (ha : Holds assetFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    recipient = noteCommitment (chunk A 27) (A 10 1010) pub.assetId (salt A 28 29) := by
  have hbind : recipient = output A 29 := by
    funext i
    exact ((digest_holds_iff pub A).mp hd |>.2.2.1 recipient hpresent i).symm
  exact hbind.trans (recipient_hash pub A hvariant hs ha hpo hb)

#print axioms note_of_blocks
#print axioms change_public
#print axioms recipient_public
end AspisR1.OutputNotes
