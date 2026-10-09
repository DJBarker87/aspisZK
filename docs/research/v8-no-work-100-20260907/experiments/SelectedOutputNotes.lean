import SelectedNoteRecovery

/-! Selected transfer output-note openings, using the actual decoder's
owner/amount/split-salt cells. The hypotheses are individual model gate,
schedule, copy and public-binding residuals, not an accepted proof or a
valid witness. Reuses the V7/V5 deterministic two-round/sponge bridges;
Rust gate/constants and complete-validator refinement remain separate. -/
set_option autoImplicit false
namespace AspisV8.SelectedOutputNotes
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedNoteRecovery

def ownerRow (block : Nat) : Nat := 16*block+12
def amountRow (block : Nat) : Nat := 16*(block+1)+12
def saltCell (block : Nat) (i : Fin 8) : Nat × Nat :=
  if i.val<6 then (amountRow block,i.val+2) else (16*(block+2)+12,i.val-6)

structure NoteFields where
  ownerKey : Digest
  value : Nat
  salt : Digest

/-- The literal decoder helper after the canonical M31/shape precheck.
Its caller uses block27 for recipient and block30 for change. -/
def decodeNote (t : Table) (block : Nat) : NoteFields where
  ownerKey := fun i=>t (ownerRow block) i.val
  value := (t (amountRow block) 0).val
  salt := fun i=>t (saltCell block i).1 (saltCell block i).2

def recordedCommitment (t : Table) (block : Nat) : Digest :=
  truncate8 (finalState t (block+2))

/-- The two full-state carry links have weight1 in the transfer variant.
Only the six *required* final rate-chunk zeros are needed by the hash proof;
unneeded high-lane zeros remain part of source semantics, not omitted checks. -/
structure OutputResiduals (rc : RoundConstants) (t : Table) (block : Nat) : Prop where
  pairs : ∀ j : Fin 3,BlockResiduals rc t (block+j.val)
  initial : ∀ i : Fin 16,t (16*block) i.val-initState DOM_NOTE 18 i=0
  carry : ∀ j : Fin 2,∀ i : Fin 16,
    t (16*(block+j.val)+11) i.val-t (16*(block+j.val+1)) i.val=0
  tailZero : ∀ i : Fin 6,t (16*(block+2)+12) (i.val+2)=0

theorem first_chunk_is_decoded (t : Table) (block : Nat) :
    chunk t block=(decodeNote t block).ownerKey := rfl

theorem second_chunk_is_decoded (t : Table) (block : Nat) :
    chunk t (block+1)=noteChunk1 ((decodeNote t block).value:F)
      (t (amountRow block) 1) (decodeNote t block).salt := by
  funext i
  fin_cases i <;>
    simp [chunk,decodeNote,ownerRow,amountRow,saltCell,noteChunk1,
      ZMod.natCast_zmod_val]

theorem third_chunk_is_decoded (rc : RoundConstants) (t : Table) (block : Nat)
    (h : OutputResiduals rc t block) :
    chunk t (block+2)=noteChunk2 (decodeNote t block).salt := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact h.tailZero 0
  · exact h.tailZero 1
  · exact h.tailZero 2
  · exact h.tailZero 3
  · exact h.tailZero 4
  · exact h.tailZero 5

/-- Every output note's actual three-block state chain is constructed from
pair residuals and the two selected copy edges; it is not a supplied chain. -/
theorem decoded_output_opening (rc : RoundConstants) (t : Table) (block : Nat)
    (h : OutputResiduals rc t block) :
    recordedCommitment t block=noteHash rc (decodeNote t block).ownerKey
      ((decodeNote t block).value:F) (t (amountRow block) 1) (decodeNote t block).salt := by
  have c0:=blockRoundChain rc t block (h.pairs 0)
  have c1:=blockRoundChain rc t (block+1) (h.pairs 1)
  have c2:=blockRoundChain rc t (block+2) (h.pairs 2)
  rw [absorbed_from_initial t block DOM_NOTE 18 h.initial] at c0
  rw [absorbed_from_carry t block (block+1) (h.carry 0)] at c1
  rw [absorbed_from_carry t (block+1) (block+2) (h.carry 1)] at c2
  have forced:=sponge3_forces rc DOM_NOTE 18 (chunk t block) (chunk t (block+1))
    (chunk t (block+2)) (finalState t block) (finalState t (block+1))
    (finalState t (block+2)) c0 c1 c2
  rw [first_chunk_is_decoded,second_chunk_is_decoded,third_chunk_is_decoded rc t block h] at forced
  exact forced

/-- Public values are independent theorem inputs. The hypothesis records
literal binding residuals; it does not authenticate caller/account context. -/
theorem public_output_opening (rc : RoundConstants) (t : Table) (block : Nat)
    (h : OutputResiduals rc t block) (publicAsset : F) (commitment : Digest)
    (assetResidual : t (amountRow block) 1-publicAsset=0)
    (commitmentResidual : ∀ i : Fin 8,t (16*(block+2)+11) i.val-commitment i=0) :
    commitment=noteHash rc (decodeNote t block).ownerKey
      ((decodeNote t block).value:F) publicAsset (decodeNote t block).salt := by
  have committed : recordedCommitment t block=commitment :=
    funext (fun i=>sub_eq_zero.mp (commitmentResidual i))
  rw [←committed,decoded_output_opening rc t block h,sub_eq_zero.mp assetResidual]

def outputBlock : Fin 2 → Nat := ![27,30]

/-- Explicitly the selected transfer's two outputs. Recipient-only gates
are active in this variant; this is not a withdrawal theorem. -/
theorem both_transfer_output_openings (rc : RoundConstants) (t : Table)
    (h : ∀ which,OutputResiduals rc t (outputBlock which))
    (publicAsset : F) (commitments : Fin 2 → Digest)
    (assets : ∀ which,t (amountRow (outputBlock which)) 1-publicAsset=0)
    (binding : ∀ which,∀ i : Fin 8,
      t (16*(outputBlock which+2)+11) i.val-commitments which i=0) :
    ∀ which,commitments which=noteHash rc (decodeNote t (outputBlock which)).ownerKey
      ((decodeNote t (outputBlock which)).value:F) publicAsset
      (decodeNote t (outputBlock which)).salt := by
  intro which
  exact public_output_opening rc t (outputBlock which) (h which) publicAsset
    (commitments which) (assets which) (binding which)

def rawTable (raw : Nat → Nat → Nat) : Table := fun row col=>(raw row col:F)
def decodeRawNote (raw : Nat → Nat → Nat) (block : Nat) : NoteFields where
  ownerKey := fun i=>(raw (ownerRow block) i.val:F)
  value := raw (amountRow block) 0
  salt := fun i=>(raw (saltCell block i).1 (saltCell block i).2:F)

/-- Exactly the canonicality requirements for the note helper's read cells;
these follow from the full decoder precheck, not from field reduction. -/
structure CanonicalNoteCells (raw : Nat → Nat → Nat) (block : Nat) : Prop where
  owner : ∀ i : Fin 8,raw (ownerRow block) i.val<p
  amount : raw (amountRow block) 0<p
  salt : ∀ i : Fin 8,raw (saltCell block i).1 (saltCell block i).2<p

/-- Derives every note-helper canonicality premise from the full decoder's
bounded1024x16 precheck. No out-of-range or fallback cell is read. -/
theorem note_cells_of_canonical_table (raw : Nat → Nat → Nat) (block : Nat)
    (hb : block≤30)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p) :
    CanonicalNoteCells raw block := by
  constructor
  · intro i
    exact canonical (ownerRow block) (by unfold ownerRow; omega) i.val (by omega)
  · exact canonical (amountRow block) (by unfold amountRow; omega) 0 (by decide)
  · intro i
    unfold saltCell
    split_ifs with head
    · exact canonical (amountRow block) (by unfold amountRow; omega) (i.val+2) (by omega)
    · exact canonical (16*(block+2)+12) (by omega) (i.val-6) (by omega)

theorem canonical_decoder_fields (raw : Nat → Nat → Nat) (block : Nat)
    (canonical : CanonicalNoteCells raw block) :
    decodeNote (rawTable raw) block=decodeRawNote raw block := by
  have amountExact : (raw (amountRow block) 0:F).val=raw (amountRow block) 0 :=
    ZMod.val_natCast_of_lt canonical.amount
  simp only [decodeNote,decodeRawNote,rawTable,amountExact]

theorem canonical_digest_representatives (raw : Nat → Nat → Nat) (block : Nat)
    (canonical : CanonicalNoteCells raw block) :
    (∀ i,((decodeRawNote raw block).ownerKey i).val = raw (ownerRow block) i.val) ∧
    (∀ i,((decodeRawNote raw block).salt i).val = raw (saltCell block i).1 (saltCell block i).2) := by
  constructor
  · intro i
    exact ZMod.val_natCast_of_lt (canonical.owner i)
  · intro i
    exact ZMod.val_natCast_of_lt (canonical.salt i)

/-- Direct raw-decoder handoff, with public commitments still supplied
independently and their actual binding residuals explicitly required. -/
theorem raw_public_output_opening (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (block : Nat) (canonical : CanonicalNoteCells raw block)
    (h : OutputResiduals rc (rawTable raw) block) (publicAsset : F) (commitment : Digest)
    (assetResidual : (raw (amountRow block) 1:F)-publicAsset=0)
    (commitmentResidual : ∀ i : Fin 8,(raw (16*(block+2)+11) i.val:F)-commitment i=0) :
    commitment=noteHash rc (decodeRawNote raw block).ownerKey
      ((decodeRawNote raw block).value:F) publicAsset (decodeRawNote raw block).salt := by
  have opening:=public_output_opening rc (rawTable raw) block h publicAsset commitment
    assetResidual commitmentResidual
  rw [canonical_decoder_fields raw block canonical] at opening
  exact opening

theorem both_raw_transfer_output_openings (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (h : ∀ which,OutputResiduals rc (rawTable raw) (outputBlock which))
    (publicAsset : F) (commitments : Fin 2 → Digest)
    (assets : ∀ which,(raw (amountRow (outputBlock which)) 1:F)-publicAsset=0)
    (binding : ∀ which,∀ i : Fin 8,
      (raw (16*(outputBlock which+2)+11) i.val:F)-commitments which i=0) :
    ∀ which,commitments which=noteHash rc (decodeRawNote raw (outputBlock which)).ownerKey
      ((decodeRawNote raw (outputBlock which)).value:F) publicAsset
      (decodeRawNote raw (outputBlock which)).salt := by
  intro which
  have hb : outputBlock which≤30 := by fin_cases which <;> decide
  exact raw_public_output_opening rc raw (outputBlock which)
    (note_cells_of_canonical_table raw (outputBlock which) hb canonical)
    (h which) publicAsset (commitments which) (assets which) (binding which)

theorem selected_output_cells :
    ownerRow (outputBlock 0)=444 ∧ amountRow (outputBlock 0)=460 ∧
    saltCell (outputBlock 0) 6=(476,0) ∧ saltCell (outputBlock 0) 7=(476,1) ∧
    16*(outputBlock 0+2)+11=475 ∧
    ownerRow (outputBlock 1)=492 ∧ amountRow (outputBlock 1)=508 ∧
    saltCell (outputBlock 1) 6=(524,0) ∧ saltCell (outputBlock 1) 7=(524,1) ∧
    16*(outputBlock 1+2)+11=523 := by decide

#print axioms first_chunk_is_decoded
#print axioms second_chunk_is_decoded
#print axioms third_chunk_is_decoded
#print axioms decoded_output_opening
#print axioms public_output_opening
#print axioms both_transfer_output_openings
#print axioms note_cells_of_canonical_table
#print axioms canonical_decoder_fields
#print axioms canonical_digest_representatives
#print axioms raw_public_output_opening
#print axioms both_raw_transfer_output_openings
#print axioms selected_output_cells
end AspisV8.SelectedOutputNotes
