import R0P.Semantics
import R0P.CopyInputLinks
import R0P.Asset

/-! G9: deterministic input-note extraction against the lead's fixed model.

Model: `Semantics.lean` at 26a11aee3, SHA-256
`9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615`;
LOG: `Lead: input-note semantic model and extraction obligation`.
Block composition uses the six blocks 0, 1, 2, 3, 25, 26. Membership uses
a symbolic induction for the current digest before each of the 24 levels,
then the final transition to block 56's output. All row links are supplied
by the separately audited `CopyInputLinks` interface.

The witnesses are exactly `traceSk`, `traceSalt`, and `tracePath`.
Only already proved row equations and `CopyLinkBalance` are consumed;
the canonical permutation and its constant tables are never evaluated. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

attribute [local irreducible] poseidonPermutation merkleRootAux

private abbrev extractionChunk (A : Trace K) (block : Fin 57) : Digest K :=
  digestOf (poseidonState A block 12)

private abbrev extractionOutput (A : Trace K) (block : Fin 57) : Digest K :=
  digestOf (poseidonState A block 11)

private abbrev extractionCurrent (A : Trace K) (level : Fin 24) : Digest K :=
  fun i => A ⟨i.val + 1, by omega⟩ (pathBaseRow level)

private abbrev extractionLeft (A : Trace K) (level : Fin 24) : Digest K :=
  fun i => A (i.castAdd 21) (succRow (pathBaseRow level))

private abbrev extractionRight (A : Trace K) (level : Fin 24) : Digest K :=
  fun i => A ⟨8 + i.val, by omega⟩ (succRow (pathBaseRow level))

private theorem extraction_block_step (pub : Public K) (A : Trace K)
    (hpo : Holds poseidonScalarFamily pub A) (block : Fin 57) :
    poseidonState A block 11 =
      spongeStep (poseidonState A block 0) (extractionChunk A block) := by
  rw [poseidon_scalar_holds_output pub A hpo block]
  unfold spongeStep
  apply congrArg poseidonPermutation
  funext lane
  simp only [poseidonAbsorbedInput, absorb, extractionChunk, digestOf, poseidonState]
  split_ifs <;> rfl

private theorem extraction_initial (pub : Public K) (A : Trace K)
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

private theorem extraction_initial_owner (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) :
    poseidonState A 0 0 = spongeInit 0x4153_0001 8 := by
  rw [extraction_initial pub A hs 0 (by left; rfl)]
  rfl

private theorem extraction_initial_note (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) :
    poseidonState A 1 0 = spongeInit 0x4153_0003 18 := by
  rw [extraction_initial pub A hs 1 (by right; left; rfl)]
  rfl

private theorem extraction_initial_nullifier (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) :
    poseidonState A 25 0 = spongeInit 0x4153_0002 16 := by
  rw [extraction_initial pub A hs 25 (by right; right; left; rfl)]
  funext lane
  simp [scheduleTarget, spongeInit]

private theorem extraction_chunk_three_zero (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (i : Fin 8) (hi : 2 ≤ i.val) :
    extractionChunk A 3 i = 0 := by
  have hz := (schedule_holds_iff pub A).mp hs |>.2.2 60 (by decide)
    (i.castAdd 8) (by
      change ScheduleAbsorbs pub.variant 3 i.val
      simp [ScheduleAbsorbs, show ¬ i.val < 2 from by omega, i.isLt])
  exact hz

private theorem extraction_chunk_three (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) :
    extractionChunk A 3 = fun i : Fin 8 =>
      if h : i.val < 2 then traceSalt A ⟨i.val + 6, by omega⟩ else 0 := by
  funext i
  by_cases hi : i.val < 2
  · rw [dif_pos hi]
    unfold traceSalt
    rw [dif_neg (by omega : ¬ i.val + 6 < 6)]
    congr 1
  · rw [dif_neg hi]
    exact extraction_chunk_three_zero pub A hs i (by omega)

private theorem extraction_chunk_two (pub : Public K) (A : Trace K)
    (ha : Holds assetFamily pub A) (hv : A 0 44 = A 10 1008) :
    extractionChunk A 2 = fun i : Fin 8 =>
      if i.val = 0 then A 10 1008 else if i.val = 1 then pub.assetId
      else traceSalt A ⟨i.val - 2, by omega⟩ := by
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
      exact (asset_holds_iff pub A).mp ha |>.1
    · rw [if_neg h1]
      unfold traceSalt
      rw [dif_pos (by omega : i.val - 2 < 6)]
      change A ⟨i.val, by omega⟩ 44 = A ⟨i.val - 2 + 2, by omega⟩ 44
      exact congrArg (fun c => A c 44) (Fin.ext (by
        change i.val = i.val - 2 + 2
        omega))

private theorem extraction_path_step (pub : Public K) (A : Trace K)
    (hp : Holds pathFamily pub A) (level : Fin 24) :
    nodeCompress (extractionLeft A level) (extractionRight A level) =
      merkleStep (extractionCurrent A level) (tracePath A level).1
        (tracePath A level).2 := by
  have hh := (path_holds_iff pub A).mp hp _ (pathBaseRow_mem level)
  by_cases hb : A 0 (pathBaseRow level) = 0
  · have hl : extractionLeft A level = extractionCurrent A level := by
      funext i
      have h := hh.2.1 i
      rw [hb] at h
      simpa only [sub_zero, one_mul, sub_eq_zero, extractionLeft, extractionCurrent,
        Fin.castAdd, Fin.castLE, Fin.addNat] using h
    simp only [tracePath, if_pos hb, merkleStep, Bool.false_eq_true, ite_false]
    rw [hl]
  · have hone : A 0 (pathBaseRow level) = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hh.1).resolve_left hb)
    have hr : extractionRight A level = extractionCurrent A level := by
      funext i
      have h := hh.2.2 i
      rw [hone, one_mul] at h
      exact sub_eq_zero.mp h
    simp only [tracePath, if_neg hb, merkleStep, ite_true]
    rw [hr]
    rfl

private theorem extraction_owner (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A) :
    extractionOutput A 0 = ownerKey (traceSk A) := by
  unfold ownerKey
  change digestOf (poseidonState A 0 11) = _
  rw [extraction_block_step pub A hpo 0, extraction_initial_owner pub A hs]
  rfl

private theorem extraction_commitment (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (ha : Holds assetFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) :
    extractionOutput A 3 =
      noteCommitment (ownerKey (traceSk A)) (A 10 1008) pub.assetId (traceSalt A) := by
  obtain ⟨hc12, hc23, _, hpk, _, _, _, hv, _⟩ :=
    copy_input_note_cells_of_balance pub A hb
  have h12 : poseidonState A 2 0 = poseidonState A 1 11 := by
    funext i; exact (hc12 i).symm
  have h23 : poseidonState A 3 0 = poseidonState A 2 11 := by
    funext i; exact (hc23 i).symm
  have howner : extractionChunk A 1 = ownerKey (traceSk A) := by
    rw [← extraction_owner pub A hs hpo]
    funext i; exact (hpk i).symm
  unfold noteCommitment
  change digestOf (poseidonState A 3 11) = _
  rw [extraction_block_step pub A hpo 3, h23, extraction_block_step pub A hpo 2,
    h12, extraction_block_step pub A hpo 1, extraction_initial_note pub A hs,
    howner, extraction_chunk_two pub A ha hv, extraction_chunk_three pub A hs]

private theorem extraction_nullifier (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    extractionOutput A 26 = nullifierHash (traceSk A) (traceSalt A) := by
  obtain ⟨_, _, hcont, _, hsk, hsalt0, hsalt1, _, _⟩ :=
    copy_input_note_cells_of_balance pub A hb
  have h26 : poseidonState A 26 0 = poseidonState A 25 11 := by
    funext i; exact (hcont i).symm
  have hkey : extractionChunk A 25 = traceSk A := by
    funext i; exact (hsk i).symm
  have hsalt : extractionChunk A 26 = traceSalt A := by
    funext i
    unfold traceSalt
    by_cases hi : i.val < 6
    · rw [dif_pos hi]
      exact (hsalt0 ⟨i.val, hi⟩).symm
    · rw [dif_neg hi]
      have hh := (hsalt1 ⟨i.val - 6, by omega⟩).symm
      change A ⟨i.val - 6 + 6, by omega⟩ 428 = A ⟨i.val - 6, by omega⟩ 60 at hh
      change A ⟨i.val, by omega⟩ 428 = A ⟨i.val - 6, by omega⟩ 60
      simpa only [show i.val - 6 + 6 = i.val from by omega] using hh
  unfold nullifierHash
  change digestOf (poseidonState A 26 11) = _
  rw [extraction_block_step pub A hpo 26, h26, extraction_block_step pub A hpo 25,
    extraction_initial_nullifier pub A hs, hkey, hsalt]

private theorem extraction_node_rate_zero (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (level : Fin 24) (i : Fin 8) :
    poseidonState A (nodeBlock level) 0 (i.castAdd 8) = 0 := by
  have hdiv : (poseidonBlockRow (nodeBlock level) 0).val / 16 = (nodeBlock level).val := by
    change (16 * (nodeBlock level).val + 0) / 16 = (nodeBlock level).val
    omega
  have hmod : (poseidonBlockRow (nodeBlock level) 0).val % 16 = 0 := by
    change (16 * (nodeBlock level).val + 0) % 16 = 0
    omega
  exact ((schedule_holds_iff pub A).mp hs).2.1 _ hmod
    (by rw [hdiv]; exact nodeBlock_node level) i

private theorem extraction_node_input (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (level : Fin 24)
    (hl : ∀ i : Fin 8, extractionLeft A level i =
      poseidonState A (nodeBlock level) 12 (i.castAdd 8))
    (hr : ∀ i : Fin 8, extractionRight A level i =
      if i.val = 7 then poseidonState A (nodeBlock level) 0 ⟨8 + i.val, by omega⟩ +
        (1051521018 : K)
      else poseidonState A (nodeBlock level) 0 ⟨8 + i.val, by omega⟩) :
    poseidonAbsorbedInput A (nodeBlock level) = fun lane : Fin 16 =>
      if h : lane.val < 8 then extractionLeft A level ⟨lane.val, h⟩
      else if lane.val = 15 then extractionRight A level 7 - (1051521018 : K)
      else extractionRight A level ⟨lane.val - 8, by omega⟩ := by
  funext lane
  by_cases hlow : lane.val < 8
  · rw [dif_pos hlow]
    have hz := extraction_node_rate_zero pub A hs level ⟨lane.val, hlow⟩
    change poseidonState A (nodeBlock level) 0 lane = 0 at hz
    change (if lane.val < 8 then
      poseidonState A (nodeBlock level) 0 lane + poseidonState A (nodeBlock level) 12 lane
      else poseidonState A (nodeBlock level) 0 lane) = _
    rw [if_pos hlow, hz, zero_add]
    exact (hl ⟨lane.val, hlow⟩).symm
  · rw [dif_neg hlow]
    change (if lane.val < 8 then
      poseidonState A (nodeBlock level) 0 lane + poseidonState A (nodeBlock level) 12 lane
      else poseidonState A (nodeBlock level) 0 lane) = _
    rw [if_neg hlow]
    by_cases h15 : lane.val = 15
    · rw [if_pos h15]
      have he : lane = 15 := Fin.ext h15
      subst lane
      have hh := hr 7
      change extractionRight A level 7 = poseidonState A (nodeBlock level) 0 15 +
        (1051521018 : K) at hh
      exact (eq_sub_iff_add_eq).mpr hh.symm
    · rw [if_neg h15]
      have hh := hr ⟨lane.val - 8, by omega⟩
      have hindex : 8 + (lane.val - 8) = lane.val := by omega
      simp only [if_neg (by omega : ¬ lane.val - 8 = 7)] at hh
      simpa only [hindex] using hh.symm

private theorem extraction_node (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (level : Fin 24) :
    extractionOutput A (nodeBlock level) =
      nodeCompress (extractionLeft A level) (extractionRight A level) := by
  have hc := copy_path_cells_of_balance pub A hb level
  have hl : ∀ i : Fin 8, extractionLeft A level i =
      poseidonState A (nodeBlock level) 12 (i.castAdd 8) := by
    intro i; exact hc.1 i
  have hr : ∀ i : Fin 8, extractionRight A level i =
      if i.val = 7 then poseidonState A (nodeBlock level) 0 ⟨8 + i.val, by omega⟩ +
        (1051521018 : K)
      else poseidonState A (nodeBlock level) 0 ⟨8 + i.val, by omega⟩ := by
    intro i
    by_cases hi : i.val = 7
    · simpa only [if_pos hi, extractionRight, poseidonState, poseidonBlockRow,
        Fin.castLE, Fin.castAdd, Fin.val_zero, Nat.add_zero, Nat.zero_add,
        Nat.add_comm] using hc.2.1 i
    · simpa only [if_neg hi, add_zero, extractionRight, poseidonState, poseidonBlockRow,
        Fin.castLE, Fin.castAdd, Fin.val_zero, Nat.add_zero, Nat.zero_add,
        Nat.add_comm] using hc.2.1 i
  unfold nodeCompress
  change digestOf (poseidonState A (nodeBlock level) 11) = _
  rw [poseidon_scalar_holds_output pub A hpo (nodeBlock level),
    extraction_node_input pub A hs level hl hr]

private theorem extraction_merkle_step (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hp : Holds pathFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) (level : Fin 24) :
    extractionOutput A (nodeBlock level) =
      merkleStep (extractionCurrent A level) (tracePath A level).1 (tracePath A level).2 := by
  exact (extraction_node pub A hs hpo hb level).trans (extraction_path_step pub A hp level)

private theorem extraction_next_current (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (level : Fin 24) (hl : level.val < 23) :
    extractionOutput A (nodeBlock level) = extractionCurrent A ⟨level.val + 1, by omega⟩ := by
  funext i
  exact (copy_path_cells_of_balance pub A hb level).2.2 hl i

private theorem extraction_membership (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hp : Holds pathFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) :
    merkleRoot (extractionOutput A 3) (tracePath A) = extractionOutput A 56 := by
  have hleaf : extractionOutput A 3 = extractionCurrent A 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hleaf⟩ := copy_input_note_cells_of_balance pub A hb
    funext i
    exact hleaf i
  have hcurrent : ∀ n : Nat, ∀ hn : n < 24,
      merkleRootAux (extractionOutput A 3) (tracePath A) n = extractionCurrent A ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        rw [merkleRootAux]
        exact hleaf
    | succ n ih =>
        intro hn
        have hn' : n < 24 := by omega
        rw [merkleRootAux, dif_pos hn', ih hn']
        exact (extraction_merkle_step pub A hs hp hpo hb ⟨n, hn'⟩).symm.trans
          (extraction_next_current pub A hb ⟨n, hn'⟩ (by change n < 23; omega))
  unfold merkleRoot
  rw [merkleRootAux, dif_pos (show 23 < 24 from by omega), hcurrent 23 (by omega)]
  exact (extraction_merkle_step pub A hs hp hpo hb 23).symm

/-- The lead's exact deterministic extraction obligation. The witnesses
are the prescribed trace cells, and copy balance is the only copy premise. -/
theorem input_note_extracted (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hp : Holds pathFamily pub A)
    (hd : Holds digestFamily pub A) (ha : Holds assetFamily pub A)
    (hpo : Holds poseidonScalarFamily pub A) (hb : CopyLinkBalance pub A) :
    InputNoteExtracted pub A := by
  refine ⟨traceSk A, traceSalt A, tracePath A, ?_, ?_⟩
  · calc
      pub.nullifier = extractionOutput A 26 := by
        funext i
        exact (((digest_holds_iff pub A).mp hd).2.1 i).symm
      _ = nullifierHash (traceSk A) (traceSalt A) := extraction_nullifier pub A hs hpo hb
  · calc
      pub.anchor = extractionOutput A 56 := by
        funext i
        exact (((digest_holds_iff pub A).mp hd).1 i).symm
      _ = merkleRoot (extractionOutput A 3) (tracePath A) :=
        (extraction_membership pub A hs hp hpo hb).symm
      _ = merkleRoot
          (noteCommitment (ownerKey (traceSk A)) (A 10 1008) pub.assetId (traceSalt A))
          (tracePath A) := by rw [extraction_commitment pub A hs ha hpo hb]

#print axioms extraction_block_step
#print axioms extraction_initial
#print axioms extraction_initial_owner
#print axioms extraction_initial_note
#print axioms extraction_initial_nullifier
#print axioms extraction_chunk_three_zero
#print axioms extraction_chunk_three
#print axioms extraction_chunk_two
#print axioms extraction_path_step
#print axioms extraction_owner
#print axioms extraction_commitment
#print axioms extraction_nullifier
#print axioms extraction_node_rate_zero
#print axioms extraction_node_input
#print axioms extraction_node
#print axioms extraction_merkle_step
#print axioms extraction_next_current
#print axioms extraction_membership
#print axioms input_note_extracted
#print axioms extractionChunk
#print axioms extractionOutput
#print axioms extractionCurrent
#print axioms extractionLeft
#print axioms extractionRight
end R0P

-- Coordinator audit: the public theorem has exactly the fixed six hypotheses.
#check @R0P.input_note_extracted
