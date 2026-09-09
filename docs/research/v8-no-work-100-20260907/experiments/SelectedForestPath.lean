import SelectedPairDecoder
import AspisFormal.V7PairForestGatedMerkle
import AspisFormal.V5AcceptedSpendRelation

/-! The selected 24-level path, not the old 20-level Tag73 layout.
The sibling is decoded from the unselected auxiliary child. Individual
selected residuals and copy equations construct node inputs and round chains;
neither a correct root, an honest trace nor decoder success is assumed.
The two-round expression uses the maintained mathematical gateStep. Equality
to the compiled Rust pair evaluator/constants is a separate source boundary.
-/
set_option autoImplicit false
namespace AspisV8.SelectedForestPath
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisFormal.V7PairForestGatedMerkle AspisV5AcceptedSpendRelation
abbrev Table := Nat → Nat → F

def auxRow (level : Nat) : Nat := 913 + 16*(level/4) + 4*(level%4)
def nodeBlock (level : Nat) : Nat := if level ≤ 20 then 4+level else 33+level
def boundaryRow (level : Nat) : Nat :=
  if level = 0 then 59 else 16*nodeBlock (level-1)+11
def digest (t : Table) (row start : Nat) : Digest := fun i => t row (start+i.val)
def current (t : Table) (level : Nat) : Digest := digest t (auxRow level) 1
def left (t : Table) (level : Nat) : Digest := digest t (auxRow level+1) 0
def right (t : Table) (level : Nat) : Digest := digest t (auxRow level+1) 8
def direction (t : Table) (level : Nat) : Bool :=
  SelectedPairDecoder.selectedSide (t (auxRow level) 0)
def sibling (t : Table) (level : Nat) : Digest :=
  if direction t level then left t level else right t level
def boundary (t : Table) (level : Nat) : Digest := digest t (boundaryRow level) 0
def nodeLeft (t : Table) (level : Nat) : Digest :=
  digest t (16*nodeBlock level+12) 0
def nodeRight (t : Table) (level : Nat) : Digest := fun i =>
  t (16*nodeBlock level) (8+i.val) - if i.val=7 then NODE_TWEAK else 0
def absorbed (t : Table) (level : Nat) : State := fun i =>
  if i.val < 8 then t (16*nodeBlock level) i.val + t (16*nodeBlock level+12) i.val
  else t (16*nodeBlock level) i.val
def pairState (t : Table) (level : Nat) : Nat → State
  | 0 => absorbed t level
  | j+1 => fun i => t (16*nodeBlock level+j+1) i.val
def finalState (t : Table) (level : Nat) : State :=
  fun i => t (16*nodeBlock level+11) i.val

/-- A sufficient subset of the exact individual field residual inventory.
Other selected semantic constraints, including high absorption zeros and
padding/mask rules, are NOT asserted to disappear from the verifier. -/
structure PathResiduals (rc : RoundConstants) (t : Table) : Prop where
  bit : ∀ l : Fin 24, t (auxRow l.val) 0 * (t (auxRow l.val) 0-1) = 0
  selectedLeft : ∀ (l : Fin 24) (i : Fin 8),
    (1-t (auxRow l.val) 0)*(left t l.val i-current t l.val i) = 0
  selectedRight : ∀ (l : Fin 24) (i : Fin 8),
    t (auxRow l.val) 0*(right t l.val i-current t l.val i) = 0
  currentCopy : ∀ (l : Fin 24) (i : Fin 8), boundary t l.val i-current t l.val i=0
  leftCopy : ∀ (l : Fin 24) (i : Fin 8), left t l.val i-nodeLeft t l.val i=0
  rightCopy : ∀ (l : Fin 24) (i : Fin 8), right t l.val i-nodeRight t l.val i=0
  initialLow : ∀ (l : Fin 24) (i : Fin 8), t (16*nodeBlock l.val) i.val=0
  pairs : ∀ (l : Fin 24) (j : Fin 11) (i : Fin 16),
    pairState t l.val (j.val+1) i -
      gateStep rc (2*j.val+1) (gateStep rc (2*j.val) (pairState t l.val j.val)) i = 0

theorem exact_decoder_coordinates (l : Fin 24) :
    auxRow l.val = SelectedPairDecoder.pathRow l ∧
      912 ≤ auxRow l.val ∧ auxRow l.val+1 < 1008 := by
  exact ⟨rfl, SelectedPairDecoder.all_selected_path_reads_in_shape l⟩

theorem selected_direction_decodes (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    SelectedPairDecoder.decodeSide (t (auxRow l.val) 0) = some (direction t l.val) :=
  SelectedPairDecoder.side_decoder_of_boolean _ (h.bit l)

/-- Reuse V7's gated-selection theorem, but identify the witness with the
literal decoder's unselected child, rather than leave it existential. -/
theorem decoded_ordered_children (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    left t l.val = (if direction t l.val then sibling t l.val else current t l.val) ∧
    right t l.val = (if direction t l.val then current t l.val else sibling t l.val) := by
  obtain ⟨s, hs⟩ := gated_selected_child_forces_ordered_children
    _ (h.bit l) (current t l.val) (left t l.val) (right t l.val)
    (h.selectedLeft l) (h.selectedRight l)
  rcases hs with ⟨zero, hl, _⟩ | ⟨one, _, hr⟩
  · have hd : direction t l.val = false := by
      simp [direction, SelectedPairDecoder.selectedSide, zero]
    simp [sibling, hd, hl]
  · have hd : direction t l.val = true := by
      simp [direction, SelectedPairDecoder.selectedSide, one]
    simp [sibling, hd, hr]

theorem exact_copy_digests (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    boundary t l.val=current t l.val ∧ left t l.val=nodeLeft t l.val ∧
      right t l.val=nodeRight t l.val := by
  exact ⟨funext (fun i => sub_eq_zero.mp (h.currentCopy l i)),
    funext (fun i => sub_eq_zero.mp (h.leftCopy l i)),
    funext (fun i => sub_eq_zero.mp (h.rightCopy l i))⟩

/-- The last-limb node tweak is removed by the actual copy tuple and then
restored by nodeState. Initial low-lane zeros are required, not assumed honest. -/
theorem absorbed_is_node_input (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    absorbed t l.val = nodeState NODE_TWEAK (left t l.val) (right t l.val) := by
  have copies := exact_copy_digests rc t h l
  rw [copies.2.1, copies.2.2]
  funext i
  by_cases low : i.val < 8
  · have hz := h.initialLow l ⟨i.val, low⟩
    simpa [absorbed, nodeState, nodeLeft, digest, low] using
      congrArg (fun x : F => x+t (16*nodeBlock l.val+12) i.val) hz
  · have idx : 8+(i.val-8)=i.val := by omega
    by_cases last : i.val=15
    · simp [absorbed, nodeState, nodeRight, last]
    · have notSeven : i.val-8≠7 := by omega
      simp [absorbed, nodeState, nodeRight, low, last, notSeven, idx]

/-- Synthesize the missing intermediate Poseidon states using the reusable
two-round theorem. No permutation-correctness or RoundChain premise is supplied. -/
def roundChainOfResiduals (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    RoundChain rc (absorbed t l.val) (finalState t l.val) := by
  let rows : TwoRoundPermutationRows rc (absorbed t l.val) (finalState t l.val) := {
    row := pairState t l.val
    startResidual := by simp [pairState]
    pairResidual := by
      intro j hj
      funext i
      exact h.pairs l ⟨j, hj⟩ i
    finishResidual := by
      funext i
      change t (16*nodeBlock l.val+10+1) i.val-t (16*nodeBlock l.val+11) i.val=0
      rw [Nat.add_assoc]
      exact sub_self _ }
  exact rows.toRoundChain

theorem next_boundary_is_final (t : Table) (l : Fin 24) :
    boundary t (l.val+1) = truncate8 (finalState t l.val) := by
  funext i
  simp [boundary, boundaryRow, digest, truncate8, finalState]

/-- One actual selected path level hashes the previous block output and the
decoder's sibling in the correct order, including the pair/forest jump. -/
theorem selected_parent_step (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) (l : Fin 24) :
    boundary t (l.val+1) =
      Parent (nodeHash rc) (direction t l.val) (boundary t l.val) (sibling t l.val) := by
  have chain := roundChainOfResiduals rc t h l
  rw [absorbed_is_node_input rc t h l] at chain
  have compressed := node_gate_forces_compression rc (left t l.val) (right t l.val)
    (finalState t l.val) chain
  rw [next_boundary_is_final, compressed, (exact_copy_digests rc t h l).1]
  have ordered := decoded_ordered_children rc t h l
  rw [ordered.1, ordered.2]
  cases direction t l.val <;> simp [Parent]

/-- Reuse the generic V7/V5 hash-chain induction at depth24, not the older
Root definition frozen at20. The endpoint is trace row907, not an assumed root. -/
theorem complete_selected_path (rc : RoundConstants) (t : Table)
    (h : PathResiduals rc t) :
    boundary t 24 = Fin.foldl 24
      (fun x l => Parent (nodeHash rc) (direction t l.val) x (sibling t l.val))
      (boundary t 0) := by
  apply foldl_chain
    (fun x l => Parent (nodeHash rc) (direction t l) x (sibling t l))
    (boundary t 0) (boundary t) rfl 24
  intro l hl
  exact selected_parent_step rc t h ⟨l, hl⟩

theorem pinned_path_transitions :
    auxRow 0=913 ∧ auxRow 20=993 ∧ auxRow 21=997 ∧ auxRow 23=1005 ∧
    nodeBlock 0=4 ∧ nodeBlock 20=24 ∧ nodeBlock 21=54 ∧ nodeBlock 23=56 ∧
    boundaryRow 0=59 ∧ boundaryRow 1=75 ∧ boundaryRow 21=395 ∧
    boundaryRow 22=875 ∧ boundaryRow 24=907 := by decide

theorem all_node_cells_in_shape (l : Fin 24) :
    4 ≤ nodeBlock l.val ∧ nodeBlock l.val ≤ 56 ∧ 16*nodeBlock l.val+12 < 912 := by
  unfold nodeBlock
  split <;> omega

#print axioms selected_direction_decodes
#print axioms decoded_ordered_children
#print axioms exact_copy_digests
#print axioms absorbed_is_node_input
#print axioms roundChainOfResiduals
#print axioms selected_parent_step
#print axioms complete_selected_path
#print axioms pinned_path_transitions
#print axioms all_node_cells_in_shape
end AspisV8.SelectedForestPath
