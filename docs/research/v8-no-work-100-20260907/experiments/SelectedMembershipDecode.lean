import DecodedIndex32
import SelectedOutputNotes

/-! Same-table raw direction parsing, literal UInt32 lane index, and the
selected pair+20 lane+3 forest membership split. No decoder-success,
honest-trace, valid-witness or authenticated-root premise is assumed. The
individual modeled path residuals and literal public binding are explicit;
the actual Rust gate/parser loop translation remains a separate interface. -/
set_option autoImplicit false
namespace AspisV8.SelectedMembershipDecode
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedNoteRecovery (Table)
open AspisV8.SelectedOutputNotes (rawTable)
open AspisV8.SelectedForestPath
open AspisV8.DecodedIndex32

def rawDirection (raw : Nat → Nat → Nat) (level : Nat) : Bool :=
  decide (raw (auxRow level) 0=1)

/-- Literal raw branch order: 0→false, 1→true, otherwise failure. -/
def parseRawDirection (raw : Nat → Nat → Nat) (level : Nat) : Option Bool :=
  if raw (auxRow level) 0=0 then some false
  else if raw (auxRow level) 0=1 then some true else none

def decodedSibling (raw : Nat → Nat → Nat) (level : Nat) : Digest :=
  fun i=>(raw (auxRow level+1) ((if rawDirection raw level then 0 else 8)+i.val):F)

def laneIndex (raw : Nat → Nat → Nat) : UInt32 :=
  assemble32 (fun i=>rawDirection raw (i+1)) 20

theorem canonical_boolean_cases (value : Nat) (canonical : value<p)
    (boolean : (value:F)*((value:F)-1)=0) : value=0 ∨ value=1 := by
  rcases mul_eq_zero.mp boolean with zero | one
  · left
    have values:=congrArg ZMod.val zero
    simpa only [ZMod.val_natCast_of_lt canonical,ZMod.val_zero] using values
  · right
    have values:=congrArg ZMod.val (sub_eq_zero.mp one)
    simpa only [ZMod.val_natCast_of_lt canonical,ZMod.val_one] using values

theorem raw_path_bit_cases (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) (level : Fin 24) :
    raw (auxRow level.val) 0=0 ∨ raw (auxRow level.val) 0=1 := by
  have bound:=exact_decoder_coordinates level
  exact canonical_boolean_cases _
    (canonical _ (by omega) 0 (by decide)) (path.bit level)

theorem all_raw_directions_parse (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) (level : Fin 24) :
    parseRawDirection raw level.val=some (rawDirection raw level.val) := by
  rcases raw_path_bit_cases rc raw canonical path level with zero | one
  · simp [parseRawDirection,rawDirection,zero]
  · simp [parseRawDirection,rawDirection,one]

theorem field_direction_is_raw (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) (level : Fin 24) :
    direction (rawTable raw) level.val=rawDirection raw level.val := by
  rcases raw_path_bit_cases rc raw canonical path level with zero | one
  · simp [direction,SelectedPairDecoder.selectedSide,rawTable,rawDirection,zero]
  · simp [direction,SelectedPairDecoder.selectedSide,rawTable,rawDirection,one]

theorem sibling_is_raw_read (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) (level : Fin 24) :
    sibling (rawTable raw) level.val=decodedSibling raw level.val := by
  rw [sibling,field_direction_is_raw rc raw canonical path level]
  cases bit : rawDirection raw level.val <;>
    funext i <;> simp [decodedSibling,bit,left,right,digest,rawTable]

theorem decoded_siblings_are_canonical (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (level : Fin 24) (i : Fin 8) :
    (decodedSibling raw level.val i).val=
      raw (auxRow level.val+1) ((if rawDirection raw level.val then 0 else 8)+i.val) := by
  have bound:=exact_decoder_coordinates level
  apply ZMod.val_natCast_of_lt
  apply canonical _ (by omega) _
  cases rawDirection raw level.val <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem decoded_lane_index_contract (raw : Nat → Nat → Nat) :
    (laneIndex raw).toNat<2^20 ∧
    (∀ (i : Nat), i < 20 → (laneIndex raw).toNat.testBit i=rawDirection raw (i+1)) ∧
    (∀ (i : Nat), 20 ≤ i → (laneIndex raw).toNat.testBit i=false) :=
  selected_index_contract _

def inputPairHash (rc : RoundConstants) (raw : Nat → Nat → Nat) : Digest :=
  nodeHash rc (SelectedPairDecoder.inputPair (rawTable raw)).firstCommitment
    (SelectedPairDecoder.inputPair (rawTable raw)).secondCommitment

def decodedLaneRoot (rc : RoundConstants) (raw : Nat → Nat → Nat) : Digest :=
  Fin.foldl 20
    (fun x i=>Parent (nodeHash rc) ((laneIndex raw).toNat.testBit i.val)
      x (decodedSibling raw (i.val+1))) (inputPairHash rc raw)

def decodedForestRoot (rc : RoundConstants) (raw : Nat → Nat → Nat) : Digest :=
  Fin.foldl 3
    (fun x i=>Parent (nodeHash rc) (rawDirection raw (i.val+21))
      x (decodedSibling raw (i.val+21))) (decodedLaneRoot rc raw)

/-- The first level is the exact input pair's hash, not a second arbitrary
sibling proof. This reuses the selected node-input/row-pair construction. -/
theorem first_boundary_is_input_pair (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (path : PathResiduals rc (rawTable raw)) :
    boundary (rawTable raw) 1=inputPairHash rc raw := by
  have chain:=roundChainOfResiduals rc (rawTable raw) path ⟨0,by decide⟩
  rw [absorbed_is_node_input rc (rawTable raw) path ⟨0,by decide⟩] at chain
  have hashed:=node_gate_forces_compression rc _ _ (finalState (rawTable raw) 0) chain
  have hl : left (rawTable raw) 0=(SelectedPairDecoder.inputPair (rawTable raw)).firstCommitment := rfl
  have hr : right (rawTable raw) 0=(SelectedPairDecoder.inputPair (rawTable raw)).secondCommitment := rfl
  rw [hl,hr] at hashed
  have final : boundary (rawTable raw) 1=truncate8 (finalState (rawTable raw) 0) := by
    funext i
    simp [boundary,boundaryRow,nodeBlock,digest,truncate8,finalState]
  exact final.trans hashed

/-- The private pair side selects the actual decoded note; no commitment
equality with an honestly generated witness is supplied. -/
theorem decoded_pair_selects_input_note (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) :
    (SelectedPairDecoder.inputPair (rawTable raw)).selectedCommitment (rawDirection raw 0)=
      SelectedNoteRecovery.inputNote (rawTable raw) := by
  have ordered:=decoded_ordered_children rc (rawTable raw) path ⟨0,by decide⟩
  have copied:=(exact_copy_digests rc (rawTable raw) path ⟨0,by decide⟩).1
  have rawBit:=field_direction_is_raw rc raw canonical path ⟨0,by decide⟩
  rw [rawBit] at ordered
  have start : boundary (rawTable raw) 0=SelectedNoteRecovery.inputNote (rawTable raw) := by
    funext i
    simp [boundary,boundaryRow,digest,SelectedNoteRecovery.inputNote,truncate8,
      SelectedNoteRecovery.finalState,SelectedNoteRecovery.state]
  rw [←start,copied]
  cases bit : rawDirection raw 0
  · funext i
    have selected:=congrArg (fun d:Digest=>d i) ordered.1
    simpa [AspisPool.V7PairLeafOccupancy.PairLeaf.selectedCommitment,
      SelectedPairDecoder.inputPair,SelectedPairDecoder.readDigest,left,digest,auxRow,bit] using selected
  · funext i
    have selected:=congrArg (fun d:Digest=>d i) ordered.2
    simpa [AspisPool.V7PairLeafOccupancy.PairLeaf.selectedCommitment,
      SelectedPairDecoder.inputPair,SelectedPairDecoder.readDigest,right,digest,auxRow,bit] using selected

theorem decoded_lane_root_is_boundary21 (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) :
    decodedLaneRoot rc raw=boundary (rawTable raw) 21 := by
  symm
  apply foldl_chain
    (fun x i=>Parent (nodeHash rc) ((laneIndex raw).toNat.testBit i)
      x (decodedSibling raw (i+1)))
    (inputPairHash rc raw) (fun i=>boundary (rawTable raw) (i+1))
    (first_boundary_is_input_pair rc raw path) 20
  intro i hi
  have step:=selected_parent_step rc (rawTable raw) path ⟨i+1,by omega⟩
  rw [field_direction_is_raw rc raw canonical path ⟨i+1,by omega⟩,
    sibling_is_raw_read rc raw canonical path ⟨i+1,by omega⟩] at step
  rw [(decoded_lane_index_contract raw).2.1 i hi]
  exact step

theorem decoded_forest_root_is_boundary24 (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) :
    decodedForestRoot rc raw=boundary (rawTable raw) 24 := by
  symm
  apply foldl_chain
    (fun x i=>Parent (nodeHash rc) (rawDirection raw (i+21))
      x (decodedSibling raw (i+21)))
    (decodedLaneRoot rc raw) (fun i=>boundary (rawTable raw) (i+21))
    (decoded_lane_root_is_boundary21 rc raw canonical path).symm 3
  intro i hi
  have step:=selected_parent_step rc (rawTable raw) path ⟨i+21,by omega⟩
  rw [field_direction_is_raw rc raw canonical path ⟨i+21,by omega⟩,
    sibling_is_raw_read rc raw canonical path ⟨i+21,by omega⟩] at step
  exact step

/-- The public root is independently supplied. This is the literal row907
binding residual, not an assumption that the already computed root is right. -/
theorem decoded_membership_public_anchor (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw)) (publicAnchor : Digest)
    (binding : ∀ i : Fin 8,(raw 907 i.val:F)-publicAnchor i=0) :
    decodedForestRoot rc raw=publicAnchor := by
  rw [decoded_forest_root_is_boundary24 rc raw canonical path]
  funext i
  simpa [boundary,boundaryRow,nodeBlock,digest,rawTable] using sub_eq_zero.mp (binding i)

/-- Reuse the already proved occupancy parser on the same raw table and
identify its selected side with the literal canonical raw direction. -/
theorem same_raw_input_pair_checked (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw))
    (pair : SelectedPairDecoder.InputPairResiduals (rawTable raw) NODE_TWEAK) :
    SelectedPairDecoder.decodeInputPairFields (rawTable raw)=
      some (SelectedPairDecoder.inputPair (rawTable raw),rawDirection raw 0) := by
  have checked:=(SelectedPairDecoder.residuals_imply_checked_input_decode
    (rawTable raw) NODE_TWEAK pair).1
  have side:=field_direction_is_raw rc raw canonical path 0
  change SelectedPairDecoder.selectedSide ((rawTable raw) 913 0)=rawDirection raw 0 at side
  rw [side] at checked
  exact checked

/-- The already derived owner/key/note/nullifier equations now join the
literal raw index/sibling membership path. Public bindings remain separate
inputs; the theorem does not authenticate caller/account data itself. -/
theorem same_decoded_note_nullifier_and_anchor (rc : RoundConstants) (raw : Nat → Nat → Nat)
    (canonical : ∀ row,row<1024 → ∀ col,col<16 → raw row col<p)
    (path : PathResiduals rc (rawTable raw))
    (notes : SelectedNoteRecovery.NoteResiduals rc (rawTable raw))
    (publicAsset : F) (publicNullifier publicAnchor : Digest)
    (assetBinding : (raw 44 1:F)-publicAsset=0)
    (nullifierBinding : ∀ i : Fin 8,(raw 427 i.val:F)-publicNullifier i=0)
    (anchorBinding : ∀ i : Fin 8,(raw 907 i.val:F)-publicAnchor i=0) :
    (SelectedPairDecoder.inputPair (rawTable raw)).selectedCommitment (rawDirection raw 0)=
      noteHash rc (ownerHash rc (SelectedNoteRecovery.key (rawTable raw)))
        (raw 44 0:F) publicAsset (SelectedNoteRecovery.salt (rawTable raw)) ∧
    publicNullifier=nullifierHash rc (SelectedNoteRecovery.key (rawTable raw))
      (SelectedNoteRecovery.salt (rawTable raw)) ∧
    decodedForestRoot rc raw=publicAnchor := by
  have hashes:=SelectedNoteRecovery.exact_public_asset_nullifier rc (rawTable raw) notes
    publicAsset publicNullifier assetBinding nullifierBinding
  exact ⟨(decoded_pair_selects_input_note rc raw canonical path).trans hashes.1,hashes.2,
    decoded_membership_public_anchor rc raw canonical path publicAnchor anchorBinding⟩

#print axioms canonical_boolean_cases
#print axioms raw_path_bit_cases
#print axioms all_raw_directions_parse
#print axioms field_direction_is_raw
#print axioms sibling_is_raw_read
#print axioms decoded_siblings_are_canonical
#print axioms decoded_lane_index_contract
#print axioms first_boundary_is_input_pair
#print axioms decoded_pair_selects_input_note
#print axioms decoded_lane_root_is_boundary21
#print axioms decoded_forest_root_is_boundary24
#print axioms decoded_membership_public_anchor
#print axioms same_raw_input_pair_checked
#print axioms same_decoded_note_nullifier_and_anchor
end AspisV8.SelectedMembershipDecode
