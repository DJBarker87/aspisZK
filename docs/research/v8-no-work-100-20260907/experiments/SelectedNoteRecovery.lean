import SelectedForestPath

/-! Selected decoder fields to owner/input-note/nullifier hashes.
All hypotheses are individual field residuals at the named selected rows.
The row-pair expression uses maintained gateStep(rc), not a claimed Rust
translation. No honest trace, supplied hash equality, successful decoding,
valid witness, or nonzero secret coordinate is assumed.
-/
set_option autoImplicit false
namespace AspisV8.SelectedNoteRecovery
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
abbrev Table := SelectedForestPath.Table
def state (t : Table) (row : Nat) : State := fun i => t row i.val
def chunk (t : Table) (block : Nat) : Digest := fun i => t (16*block+12) i.val
def finalState (t : Table) (block : Nat) : State := state t (16*block+11)
def absorbed (t : Table) (block : Nat) : State := absorb (state t (16*block)) (chunk t block)
def pairState (t : Table) (block : Nat) : Nat → State
  | 0 => absorbed t block
  | j+1 => state t (16*block+j+1)
def key (t : Table) : Digest := chunk t 0
def amount (t : Table) : F := t 44 0
def asset (t : Table) : F := t 44 1
def salt (t : Table) : Digest := fun i =>
  if i.val < 6 then t 44 (i.val+2) else t 60 (i.val-6)
def owner (t : Table) : Digest := truncate8 (finalState t 0)
def inputNote (t : Table) : Digest := truncate8 (finalState t 3)
def nullifier (t : Table) : Digest := truncate8 (finalState t 26)
def activeBlocks : Finset Nat := {0,1,2,3,25,26}

def BlockResiduals (rc : RoundConstants) (t : Table) (block : Nat) : Prop :=
  ∀ (j : Fin 11) (i : Fin 16), pairState t block (j.val+1) i -
    gateStep rc (2*j.val+1) (gateStep rc (2*j.val) (pairState t block j.val)) i = 0

/-- Sufficient selected residual subset for six sponge blocks. The initial
row expression is the exact domain/length layout, not an assumed hash. -/
structure NoteResiduals (rc : RoundConstants) (t : Table) : Prop where
  pairs : ∀ block, block ∈ activeBlocks → BlockResiduals rc t block
  initialOwner : ∀ i : Fin 16, t 0 i.val-initState DOM_OWNER 8 i=0
  initialNote : ∀ i : Fin 16, t 16 i.val-initState DOM_NOTE 18 i=0
  initialNullifier : ∀ i : Fin 16, t 400 i.val-initState DOM_NULLIFIER 16 i=0
  carryNote1 : ∀ i : Fin 16, t 27 i.val-t 32 i.val=0
  carryNote2 : ∀ i : Fin 16, t 43 i.val-t 48 i.val=0
  carryNullifier : ∀ i : Fin 16, t 411 i.val-t 416 i.val=0
  ownerCopy : ∀ i : Fin 8, t 11 i.val-t 28 i.val=0
  keyCopy : ∀ i : Fin 8, t 12 i.val-t 412 i.val=0
  saltHeadCopy : ∀ i : Fin 6, t 44 (i.val+2)-t 428 i.val=0
  saltTailCopy : ∀ i : Fin 2, t 60 i.val-t 428 (i.val+6)=0
  noteTailZero : ∀ i : Fin 6, t 60 (i.val+2)=0

/-- The same reusable two-round conversion used by V7. Missing odd states
are computed from the row gate; they are not additional witnesses. -/
def blockRoundChain (rc : RoundConstants) (t : Table) (block : Nat)
    (h : BlockResiduals rc t block) :
    RoundChain rc (absorbed t block) (finalState t block) := by
  let rows : TwoRoundPermutationRows rc (absorbed t block) (finalState t block) := {
    row := pairState t block
    startResidual := by simp [pairState]
    pairResidual := by
      intro j hj
      funext i
      exact h ⟨j,hj⟩ i
    finishResidual := by
      funext i
      change t (16*block+10+1) i.val-t (16*block+11) i.val=0
      rw [Nat.add_assoc]
      exact sub_self _ }
  exact rows.toRoundChain

theorem absorbed_from_initial (t : Table) (block : Nat) (domain len : F)
    (initial : ∀ i : Fin 16, t (16*block) i.val-initState domain len i=0) :
    absorbed t block=absorb (initState domain len) (chunk t block) := by
  have hs : state t (16*block)=initState domain len :=
    funext (fun i => sub_eq_zero.mp (initial i))
  exact congrArg (fun s => absorb s (chunk t block)) hs

theorem absorbed_from_carry (t : Table) (previous block : Nat)
    (carry : ∀ i : Fin 16, t (16*previous+11) i.val-t (16*block) i.val=0) :
    absorbed t block=absorb (finalState t previous) (chunk t block) := by
  have hs : state t (16*block)=finalState t previous :=
    funext (fun i => (sub_eq_zero.mp (carry i)).symm)
  exact congrArg (fun s => absorb s (chunk t block)) hs

theorem owner_from_decoded_key (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) : owner t=ownerHash rc (key t) := by
  have chain := blockRoundChain rc t 0 (h.pairs 0 (by decide))
  rw [absorbed_from_initial t 0 DOM_OWNER 8 h.initialOwner] at chain
  exact sponge1_forces rc DOM_OWNER 8 (key t) (finalState t 0) chain

theorem note_first_chunk_is_owner (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) : chunk t 1=ownerHash rc (key t) := by
  have copied : chunk t 1=owner t :=
    funext (fun i => (sub_eq_zero.mp (h.ownerCopy i)).symm)
  exact copied.trans (owner_from_decoded_key rc t h)

theorem note_second_chunk_is_decoded (t : Table) :
    chunk t 2=noteChunk1 (amount t) (asset t) (salt t) := by
  funext i
  fin_cases i <;> rfl

theorem note_third_chunk_is_decoded (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) : chunk t 3=noteChunk2 (salt t) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact h.noteTailZero 0
  · exact h.noteTailZero 1
  · exact h.noteTailZero 2
  · exact h.noteTailZero 3
  · exact h.noteTailZero 4
  · exact h.noteTailZero 5

theorem input_note_from_decoded_fields (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) :
    inputNote t=noteHash rc (ownerHash rc (key t)) (amount t) (asset t) (salt t) := by
  have c1 := blockRoundChain rc t 1 (h.pairs 1 (by decide))
  have c2 := blockRoundChain rc t 2 (h.pairs 2 (by decide))
  have c3 := blockRoundChain rc t 3 (h.pairs 3 (by decide))
  rw [absorbed_from_initial t 1 DOM_NOTE 18 h.initialNote] at c1
  rw [absorbed_from_carry t 1 2 h.carryNote1] at c2
  rw [absorbed_from_carry t 2 3 h.carryNote2] at c3
  have forced := sponge3_forces rc DOM_NOTE 18 (chunk t 1) (chunk t 2) (chunk t 3)
    (finalState t 1) (finalState t 2) (finalState t 3) c1 c2 c3
  rw [note_first_chunk_is_owner rc t h, note_second_chunk_is_decoded t,
    note_third_chunk_is_decoded rc t h] at forced
  exact forced

theorem nullifier_chunks_are_decoded (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) : chunk t 25=key t ∧ chunk t 26=salt t := by
  refine ⟨funext (fun i => (sub_eq_zero.mp (h.keyCopy i)).symm), ?_⟩
  funext i
  by_cases head : i.val < 6
  · simpa only [chunk, salt, if_pos head] using
      (sub_eq_zero.mp (h.saltHeadCopy ⟨i.val,head⟩)).symm
  · have tailBound : i.val-6<2 := by omega
    have index : i.val-6+6=i.val := by omega
    have copied := (sub_eq_zero.mp (h.saltTailCopy ⟨i.val-6,tailBound⟩)).symm
    simpa only [chunk, salt, if_neg head, index] using copied

theorem nullifier_from_same_decoded_key_salt (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) : nullifier t=nullifierHash rc (key t) (salt t) := by
  have c1 := blockRoundChain rc t 25 (h.pairs 25 (by decide))
  have c2 := blockRoundChain rc t 26 (h.pairs 26 (by decide))
  rw [absorbed_from_initial t 25 DOM_NULLIFIER 16 h.initialNullifier] at c1
  rw [absorbed_from_carry t 25 26 h.carryNullifier] at c2
  have forced := sponge2_forces rc DOM_NULLIFIER 16 (chunk t 25) (chunk t 26)
    (finalState t 25) (finalState t 26) c1 c2
  rw [(nullifier_chunks_are_decoded rc t h).1,
    (nullifier_chunks_are_decoded rc t h).2] at forced
  exact forced

/-- The concrete recovered key supplies the note's owner hash and the same
key/salt supplies the nullifier. This is not an assumed knowledge predicate. -/
theorem decoded_hash_endpoint (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) :
    owner t=ownerHash rc (key t) ∧
    inputNote t=noteHash rc (ownerHash rc (key t)) (amount t) (asset t) (salt t) ∧
    nullifier t=nullifierHash rc (key t) (salt t) :=
  ⟨owner_from_decoded_key rc t h, input_note_from_decoded_fields rc t h,
    nullifier_from_same_decoded_key_salt rc t h⟩

/-- Compose with the selected24-level path already proved. The conclusion
names the recorded forest endpoint, not an assumed authenticated root. -/
theorem decoded_note_reaches_recorded_forest (rc : RoundConstants) (t : Table)
    (notes : NoteResiduals rc t) (path : SelectedForestPath.PathResiduals rc t) :
    SelectedForestPath.boundary t 24 = Fin.foldl 24
      (fun x l => Parent (nodeHash rc) (SelectedForestPath.direction t l.val)
        x (SelectedForestPath.sibling t l.val))
      (noteHash rc (ownerHash rc (key t)) (amount t) (asset t) (salt t)) := by
  have start : SelectedForestPath.boundary t 0=inputNote t := by
    funext i
    simp [SelectedForestPath.boundary, SelectedForestPath.boundaryRow,
      SelectedForestPath.digest, inputNote, truncate8, finalState, state]
  rw [SelectedForestPath.complete_selected_path rc t path, start,
    input_note_from_decoded_fields rc t notes]

/-- Optional literal public residual handoff. The public parameters must
come from the caller's authenticated context; this theorem does not supply it. -/
theorem exact_public_asset_nullifier (rc : RoundConstants) (t : Table)
    (h : NoteResiduals rc t) (publicAsset : F) (publicNullifier : Digest)
    (assetResidual : t 44 1-publicAsset=0)
    (nullifierResidual : ∀ i : Fin 8, t 427 i.val-publicNullifier i=0) :
    inputNote t=noteHash rc (ownerHash rc (key t)) (amount t) publicAsset (salt t) ∧
    publicNullifier=nullifierHash rc (key t) (salt t) := by
  have ea : asset t=publicAsset := sub_eq_zero.mp assetResidual
  have en : nullifier t=publicNullifier :=
    funext (fun i => sub_eq_zero.mp (nullifierResidual i))
  exact ⟨by rw [input_note_from_decoded_fields rc t h, ea],
    en.symm.trans (nullifier_from_same_decoded_key_salt rc t h)⟩

#print axioms blockRoundChain
#print axioms owner_from_decoded_key
#print axioms note_first_chunk_is_owner
#print axioms note_second_chunk_is_decoded
#print axioms note_third_chunk_is_decoded
#print axioms input_note_from_decoded_fields
#print axioms nullifier_chunks_are_decoded
#print axioms nullifier_from_same_decoded_key_salt
#print axioms decoded_hash_endpoint
#print axioms decoded_note_reaches_recorded_forest
#print axioms exact_public_asset_nullifier
end AspisV8.SelectedNoteRecovery
