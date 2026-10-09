import SelectedOutputNotes

/-! Selected transfer output-pair construction. The change sentinel's
nonzeroness is derived from the selected occupancy/copy residuals, not an
honest salt or successful constructor. Literal tag3495's M31 offset is
normalized before constructing block33's node-hash chain. This is the
mathematical field stage; Rust canonical parsing/inversion/constants and
complete accepted-residual enforcement remain separate source boundaries. -/
set_option autoImplicit false
namespace AspisV8.SelectedOutputPair
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedNoteRecovery AspisV8.SelectedOutputNotes
open AspisPool.V7PairLeafOccupancy (PairLeaf twoOutputPair twoOutputPair_valid)

def recipient (t : Table) : Digest := recordedCommitment t 27
def change (t : Table) : Digest := recordedCommitment t 30
def pairDigest (t : Table) : Digest := truncate8 (finalState t 33)

/-- Literal compiled pattern10, including its last-limb M31 offset. -/
def rightInput (t : Table) (i : Fin 8) : F :=
  t 528 (8+i.val) + if i.val=7 then (1051521018:F) else 0

/-- A sufficient selected TRANSFER residual subset: occupancy lane11 fixes
occupied=1, lane1 certifies the inverse; tags3492/3493/3495 have their actual
transfer weights (one). No check is removed from the source verifier. -/
structure OutputPairResiduals (rc : RoundConstants) (t : Table) : Prop where
  occupied : t 1018 0-1=0
  inverse : t 1018 9*t 1018 1-t 1018 0=0
  changeCopy : ∀ i : Fin 8,t 523 i.val-t 1018 (2+i.val)=0
  recipientCopy : ∀ i : Fin 8,t 475 i.val-t 540 i.val=0
  rightCopy : ∀ i : Fin 8,t 1018 (2+i.val)-rightInput t i=0
  initialLow : ∀ i : Fin 8,t 528 i.val=0
  pairs : BlockResiduals rc t 33

/-- Reuses the exact symbolic cast argument of the pinned V7
`right_offset_cancels_node_tweak`, without importing its unrelated trace
extraction closure or reducing a giant concrete ZMod expression. -/
theorem literal_right_offset_cancels : (1051521018:F)+NODE_TWEAK=0 := by
  rw [NODE_TWEAK]
  change ((1051521018:Nat):F)+((1095962629:Nat):F)=0
  rw [←Nat.cast_add]
  change ((2147483647:Nat):ZMod 2147483647)=0
  exact ZMod.natCast_self 2147483647

theorem actual_change_inverse (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) : change t 7*t 1018 1=1 := by
  have copied : change t 7=t 1018 9 := sub_eq_zero.mp (h.changeCopy 7)
  rw [copied,sub_eq_zero.mp h.inverse,sub_eq_zero.mp h.occupied]

theorem output_pair_valid (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) :
    (twoOutputPair (recipient t) (change t) (t 1018 1)).Valid :=
  twoOutputPair_valid _ _ _ (actual_change_inverse rc t h)

/-- The maintained V7 theorem discharges the genuine occupied-sentinel
rejection branch. No individual digest coordinate is assumed nonzero. -/
theorem actual_change_sentinel_nonzero (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) : change t 7≠0 := by
  exact AspisPool.V7PairLeafOccupancy.valid_occupied_second_sentinel_ne_zero
    (twoOutputPair (recipient t) (change t) (t 1018 1))
    (output_pair_valid rc t h) rfl

theorem actual_inverse_is_computed_inverse (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) : t 1018 1=(change t 7)⁻¹ := by
  apply mul_left_cancel₀ (actual_change_sentinel_nonzero rc t h)
  rw [actual_change_inverse rc t h,mul_inv_cancel₀ (actual_change_sentinel_nonzero rc t h)]

def computedPair (left right : Digest) : PairLeaf F :=
  twoOutputPair left right (right 7)⁻¹

/-- Field-stage branch order of `PoolV1PairLeafWitnessV1::two_outputs`:
reject a zero sentinel, compute its inverse, and validate the resulting pair.
The source raw-canonicality precheck precedes this mathematical model. -/
def twoOutputsFields (left right : Digest) : Option (PairLeaf F) :=
  if right 7=0 then none else
    if SelectedPairDecoder.validatePairFields (computedPair left right)=some () then
      some (computedPair left right)
    else none

theorem nonzero_two_outputs_checked (left right : Digest) (nonzero : right 7≠0) :
    twoOutputsFields left right=some (computedPair left right) := by
  have valid : (computedPair left right).Valid :=
    twoOutputPair_valid left right (right 7)⁻¹ (mul_inv_cancel₀ nonzero)
  have checked := SelectedPairDecoder.v7_valid_implies_field_validator _ valid
  simp only [twoOutputsFields,if_neg nonzero,checked,ite_true]

theorem actual_two_outputs_checked (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) :
    twoOutputsFields (recipient t) (change t)=
      some (twoOutputPair (recipient t) (change t) (t 1018 1)) := by
  rw [nonzero_two_outputs_checked _ _ (actual_change_sentinel_nonzero rc t h),
    actual_inverse_is_computed_inverse rc t h]
  rfl

theorem pair_input_aliases (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) :
    (∀ i : Fin 8,t 540 i.val=recipient t i) ∧
    (∀ i : Fin 8,t 528 (8+i.val)=change t i+if i.val=7 then NODE_TWEAK else 0) := by
  refine ⟨fun i=>(sub_eq_zero.mp (h.recipientCopy i)).symm,?_⟩
  intro i
  have equal : change t i=rightInput t i :=
    (sub_eq_zero.mp (h.changeCopy i)).trans (sub_eq_zero.mp (h.rightCopy i))
  by_cases last : i.val=7
  · have ht : (1051521018:F)=-NODE_TWEAK :=
      eq_neg_iff_add_eq_zero.mpr literal_right_offset_cancels
    simpa only [rightInput,if_pos last,ht,sub_eq_add_neg,add_assoc,neg_add_cancel,add_zero]
      using congrArg (fun x:F=>x+NODE_TWEAK) equal.symm
  · simpa only [rightInput,if_neg last,add_zero] using equal.symm

/-- Generic rate-eight node-input interface. The low zeros and both child
arrays come from the selected aliases when instantiated below. -/
theorem node_absorption_from_cells (t : Table) (block : Nat) (left right : Digest)
    (lowZero : ∀ i : Fin 8,t (16*block) i.val=0)
    (leftCells : ∀ i : Fin 8,t (16*block+12) i.val=left i)
    (rightCells : ∀ i : Fin 8,
      t (16*block) (8+i.val)=right i+if i.val=7 then NODE_TWEAK else 0) :
    absorbed t block=nodeState NODE_TWEAK left right := by
  funext i
  by_cases low : i.val<8
  · simp only [absorbed,absorb,state,chunk,low,dif_pos,nodeState,
      lowZero ⟨i.val,low⟩,leftCells ⟨i.val,low⟩,zero_add]
  · have jBound : i.val-8<8 := by omega
    have index : 8+(i.val-8)=i.val := by omega
    have high:=rightCells ⟨i.val-8,jBound⟩
    rw [index] at high
    by_cases last : i.val=15
    · have seven : i.val-8=7 := by omega
      simpa [absorbed,absorb,state,chunk,low,nodeState,last,seven] using high
    · have notSeven : i.val-8≠7 := by omega
      simpa [absorbed,absorb,state,chunk,low,nodeState,last,notSeven] using high

theorem pair_digest_is_ordered_outputs (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) :
    pairDigest t=nodeHash rc (recipient t) (change t) := by
  have aliases:=pair_input_aliases rc t h
  have input:=node_absorption_from_cells t 33 (recipient t) (change t)
    h.initialLow aliases.1 aliases.2
  have chain:=blockRoundChain rc t 33 h.pairs
  rw [input] at chain
  exact node_gate_forces_compression rc _ _ (finalState t 33) chain

/-- Public commitments are independent caller inputs. Their literal
vanishing digest residuals provide equality, not their authority. -/
theorem public_output_pair_endpoint (rc : RoundConstants) (t : Table)
    (h : OutputPairResiduals rc t) (publicRecipient publicChange : Digest)
    (recipientBinding : ∀ i : Fin 8,t 475 i.val-publicRecipient i=0)
    (changeBinding : ∀ i : Fin 8,t 523 i.val-publicChange i=0) :
    publicChange 7≠0 ∧
    twoOutputsFields publicRecipient publicChange=some (computedPair publicRecipient publicChange) ∧
    pairDigest t=nodeHash rc publicRecipient publicChange := by
  have hl : recipient t=publicRecipient := funext (fun i=>sub_eq_zero.mp (recipientBinding i))
  have hr : change t=publicChange := funext (fun i=>sub_eq_zero.mp (changeBinding i))
  have nonzero:=actual_change_sentinel_nonzero rc t h
  rw [hr] at nonzero
  refine ⟨nonzero,nonzero_two_outputs_checked _ _ nonzero,?_⟩
  rw [pair_digest_is_ordered_outputs rc t h,hl,hr]

/-- Consume the newly proved same-table output openings: both decoded note
hashes feed the pair hash and satisfy its actual sentinel construction gate.
The theorem does not supply a compiler/validator success premise. -/
theorem decoded_outputs_feed_checked_pair (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (notes : ∀ which,OutputResiduals rc (rawTable raw) (outputBlock which))
    (pair : OutputPairResiduals rc (rawTable raw))
    (publicAsset : F) (commitments : Fin 2 → Digest)
    (assets : ∀ which,(raw (amountRow (outputBlock which)) 1:F)-publicAsset=0)
    (binding : ∀ which,∀ i : Fin 8,
      (raw (16*(outputBlock which+2)+11) i.val:F)-commitments which i=0) :
    (∀ which,commitments which=noteHash rc (decodeRawNote raw (outputBlock which)).ownerKey
      ((decodeRawNote raw (outputBlock which)).value:F) publicAsset
      (decodeRawNote raw (outputBlock which)).salt) ∧
    commitments 1 7≠0 ∧
    twoOutputsFields (commitments 0) (commitments 1)=
      some (computedPair (commitments 0) (commitments 1)) ∧
    pairDigest (rawTable raw)=nodeHash rc (commitments 0) (commitments 1) := by
  exact ⟨both_raw_transfer_output_openings rc raw canonical notes publicAsset commitments assets binding,
    public_output_pair_endpoint rc (rawTable raw) pair (commitments 0) (commitments 1)
      (binding 0) (binding 1)⟩

#print axioms literal_right_offset_cancels
#print axioms actual_change_inverse
#print axioms output_pair_valid
#print axioms actual_change_sentinel_nonzero
#print axioms actual_inverse_is_computed_inverse
#print axioms nonzero_two_outputs_checked
#print axioms actual_two_outputs_checked
#print axioms pair_input_aliases
#print axioms node_absorption_from_cells
#print axioms pair_digest_is_ordered_outputs
#print axioms public_output_pair_endpoint
#print axioms decoded_outputs_feed_checked_pair
end AspisV8.SelectedOutputPair
