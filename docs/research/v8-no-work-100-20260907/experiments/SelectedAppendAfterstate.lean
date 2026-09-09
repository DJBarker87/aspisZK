import SelectedOutputPair

/-! The selected twenty-block append, consuming the SAME recovered table as
the output-pair endpoint. Individual gated copy/public-digest residuals build
the ordered node inputs and round chains. The complete proposed frontier is
then determined by the source's static checks and its one dynamic carry
binding. This does not assume compiler/append success, rehash an old root the
source does not check, or establish authority of the supplied live snapshot.
The bounded Boolean carry scan is modeled explicitly; translating Rust's u64
trailing_ones intrinsic and literal field/Poseidon instructions remains open. -/
set_option autoImplicit false
namespace AspisV8.SelectedAppendAfterstate
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV8.SelectedNoteRecovery AspisV8.SelectedOutputPair

/-- An ascending bounded scan, stopping at the first zero. No challenge or
prover-selected carry index is supplied to the endpoint. -/
def carryScan (bits : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => if carryScan bits n=n ∧ bits n=true then n+1 else carryScan bits n

theorem carry_scan_bound (bits : Nat → Bool) (n : Nat) : carryScan bits n≤n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [carryScan]
      split <;> omega

theorem carry_scan_spec (bits : Nat → Bool) (n : Nat) :
    (∀ i<carryScan bits n,bits i=true) ∧
      (carryScan bits n<n → bits (carryScan bits n)=false) := by
  induction n with
  | zero => simp [carryScan]
  | succ n ih =>
      have bound:=carry_scan_bound bits n
      by_cases active : carryScan bits n=n ∧ bits n=true
      · rw [carryScan,if_pos active]
        constructor
        · intro i hi
          by_cases last : i=n
          · simpa only [last] using active.2
          · exact ih.1 i (by omega)
        · omega
      · rw [carryScan,if_neg active]
        refine ⟨ih.1,?_⟩
        intro _
        by_cases stopped : carryScan bits n<n
        · exact ih.2 stopped
        · have same : carryScan bits n=n := by omega
          have notOne : bits n≠true := fun h=>active ⟨same,h⟩
          simpa only [same] using Bool.eq_false_iff.mpr notOne

def carryIndex (index : Nat) : Nat := carryScan index.testBit 20
def boundary (t : Table) (level : Nat) : Digest :=
  fun i=>t (539+16*level) i.val
def nodeLeft (t : Table) (level : Nat) : Digest :=
  fun i=>t (556+16*level) i.val
def literalRight (t : Table) (level : Nat) : Digest :=
  fun i=>t (544+16*level) (8+i.val)+if i.val=7 then (1051521018:F) else 0
def nodeRight (t : Table) (level : Nat) : Digest :=
  fun i=>t (544+16*level) (8+i.val)-if i.val=7 then NODE_TWEAK else 0

theorem right_pattern_is_untweaked (t : Table) (level : Nat) :
    literalRight t level=nodeRight t level := by
  have offset : (1051521018:F)=-NODE_TWEAK :=
    eq_neg_iff_add_eq_zero.mpr literal_right_offset_cancels
  funext i
  by_cases last : i.val=7 <;> simp [literalRight,nodeRight,last,offset,sub_eq_add_neg]

/-- Sufficient individual selected constraints. The two gated copy families
are literal tags1124073496+2*l and1124073497+2*l; sibling bindings are the
complementary public digest checks. Other verifier residuals are not removed.
Each digest's eight coefficient constraints are prerequisites, not inferred
here from equality at a random lambda. -/
structure AppendResiduals (rc : RoundConstants) (t : Table)
    (index : Nat) (empty frontier : Nat → Digest) : Prop where
  currentLeft : ∀ (l : Fin 20) (i : Fin 8),
    (if index.testBit l.val then (0:F) else 1)*
      (boundary t l.val i-nodeLeft t l.val i)=0
  currentRight : ∀ (l : Fin 20) (i : Fin 8),
    (if index.testBit l.val then (1:F) else 0)*
      (boundary t l.val i-literalRight t l.val i)=0
  emptyRight : ∀ (l : Fin 20),index.testBit l.val=false →
    ∀ i : Fin 8,t (544+16*l.val) (8+i.val)-
      (empty l.val i+if i.val=7 then NODE_TWEAK else 0)=0
  liveLeft : ∀ (l : Fin 20),index.testBit l.val=true →
    ∀ i : Fin 8,nodeLeft t l.val i-frontier l.val i=0
  initialLow : ∀ (l : Fin 20) (i : Fin 8),t (16*(34+l.val)) i.val=0
  pairs : ∀ l : Fin 20,BlockResiduals rc t (34+l.val)

theorem ordered_append_children (rc : RoundConstants) (t : Table)
    (index : Nat) (empty frontier : Nat → Digest)
    (h : AppendResiduals rc t index empty frontier) (l : Fin 20) :
    nodeLeft t l.val=(if index.testBit l.val then frontier l.val else boundary t l.val) ∧
    nodeRight t l.val=(if index.testBit l.val then boundary t l.val else empty l.val) := by
  have right:=right_pattern_is_untweaked t l.val
  cases bit : index.testBit l.val with
  | false =>
      simp only [bit,Bool.false_eq_true,if_false]
      constructor
      · funext i
        have copy:=h.currentLeft l i
        simp only [bit,Bool.false_eq_true,if_false,one_mul] at copy
        exact (sub_eq_zero.mp copy).symm
      · funext i
        change t (544+16*l.val) (8+i.val)-
          (if i.val=7 then NODE_TWEAK else 0)=empty l.val i
        rw [sub_eq_zero.mp (h.emptyRight l bit i),add_sub_cancel_right]
  | true =>
      simp only [bit,if_true]
      constructor
      · exact funext (fun i=>sub_eq_zero.mp (h.liveLeft l bit i))
      · rw [←right]
        funext i
        have copy:=h.currentRight l i
        simp only [bit,if_true,one_mul] at copy
        exact (sub_eq_zero.mp copy).symm

theorem append_node_input (rc : RoundConstants) (t : Table)
    (index : Nat) (empty frontier : Nat → Digest)
    (h : AppendResiduals rc t index empty frontier) (l : Fin 20) :
    absorbed t (34+l.val)=nodeState NODE_TWEAK (nodeLeft t l.val) (nodeRight t l.val) := by
  apply node_absorption_from_cells t (34+l.val) _ _ (h.initialLow l)
  · intro i
    change t (16*(34+l.val)+12) i.val=t (556+16*l.val) i.val
    congr 1 <;> omega
  · intro i
    change t (16*(34+l.val)) (8+i.val)=
      (t (544+16*l.val) (8+i.val)-(if i.val=7 then NODE_TWEAK else 0))+
        (if i.val=7 then NODE_TWEAK else 0)
    have row : 16*(34+l.val)=544+16*l.val := by omega
    rw [row,sub_add_cancel]

def appendStep (rc : RoundConstants) (index : Nat) (empty frontier : Nat → Digest)
    (carry : Digest) (level : Nat) : Digest :=
  if index.testBit level then nodeHash rc (frontier level) carry
  else nodeHash rc carry (empty level)

theorem append_parent_step (rc : RoundConstants) (t : Table)
    (index : Nat) (empty frontier : Nat → Digest)
    (h : AppendResiduals rc t index empty frontier) (l : Fin 20) :
    boundary t (l.val+1)=appendStep rc index empty frontier (boundary t l.val) l.val := by
  have chain:=blockRoundChain rc t (34+l.val) (h.pairs l)
  rw [append_node_input rc t index empty frontier h l] at chain
  have hash:=node_gate_forces_compression rc _ _ (finalState t (34+l.val)) chain
  have rows : boundary t (l.val+1)=truncate8 (finalState t (34+l.val)) := by
    funext i
    change t (539+16*(l.val+1)) i.val=t (16*(34+l.val)+11) i.val
    congr 1 <;> omega
  rw [rows,hash,(ordered_append_children rc t index empty frontier h l).1,
    (ordered_append_children rc t index empty frontier h l).2]
  cases bit : index.testBit l.val <;> simp [appendStep,bit]

def computedAt (rc : RoundConstants) (index : Nat) (empty frontier : Nat → Digest)
    (leaf : Digest) (level : Nat) : Digest :=
  Fin.foldl level (fun x l=>appendStep rc index empty frontier x l.val) leaf

theorem all_append_boundaries (rc : RoundConstants) (t : Table)
    (index : Nat) (empty frontier : Nat → Digest)
    (h : AppendResiduals rc t index empty frontier) (n : Nat) (hn : n≤20) :
    boundary t n=computedAt rc index empty frontier (pairDigest t) n := by
  apply foldl_chain
    (fun x l=>appendStep rc index empty frontier x l) (pairDigest t) (boundary t) rfl n
  intro l hl
  exact append_parent_step rc t index empty frontier h ⟨l,by omega⟩

def computedFrontier (rc : RoundConstants) (index : Nat) (empty frontier : Nat → Digest)
    (leaf : Digest) (level : Nat) : Digest :=
  if level<carryIndex index then empty level
  else if level=carryIndex index ∧ carryIndex index<20 then
    computedAt rc index empty frontier leaf level
  else if index.testBit level then frontier level else empty level

/-- Exact split of validate_transition's direct checks and public_digest_lanes'
dynamic carry/root bindings. Equality of pool/deployment with an independently
authenticated caller is external to this algebraic afterstate predicate.
Index guards are integer equalities, not equalities modulo M31. -/
structure AfterstateChecks (t : Table) (sequence index nextIndex : Nat)
    (empty frontier nextFrontier : Nat → Digest) (nextRoot : Digest) : Prop where
  sequenceIndex : sequence=index
  notFull : index<2^20
  increment : nextIndex=index+1
  staticFrontier : ∀ l : Fin 20,l.val≠carryIndex index →
    nextFrontier l.val=if l.val<carryIndex index ∨ index.testBit l.val=false then
      empty l.val else frontier l.val
  carryBinding : carryIndex index<20 → ∀ i : Fin 8,
    boundary t (carryIndex index) i-nextFrontier (carryIndex index) i=0
  rootBinding : ∀ i : Fin 8,t 859 i.val-nextRoot i=0

theorem entire_afterstate_forced (rc : RoundConstants) (t : Table)
    (sequence index nextIndex : Nat) (empty frontier nextFrontier : Nat → Digest)
    (nextRoot : Digest) (h : AppendResiduals rc t index empty frontier)
    (checked : AfterstateChecks t sequence index nextIndex empty frontier nextFrontier nextRoot) :
    nextIndex=sequence+1 ∧ nextIndex≤2^20 ∧
    nextRoot=computedAt rc index empty frontier (pairDigest t) 20 ∧
    (∀ l : Fin 20,nextFrontier l.val=
      computedFrontier rc index empty frontier (pairDigest t) l.val) := by
  refine ⟨by rw [checked.sequenceIndex,checked.increment],by
    have := checked.notFull
    rw [checked.increment]
    omega,?_,?_⟩
  · have root : boundary t 20=nextRoot := funext (fun i=>sub_eq_zero.mp (checked.rootBinding i))
    exact root.symm.trans (all_append_boundaries rc t index empty frontier h 20 (by omega))
  · intro l
    by_cases carry : l.val=carryIndex index
    · have below : carryIndex index<20 := by omega
      have cell : boundary t (carryIndex index)=nextFrontier (carryIndex index) :=
        funext (fun i=>sub_eq_zero.mp (checked.carryBinding below i))
      rw [carry]
      simp only [computedFrontier,lt_self_iff_false,if_false,true_and,below,if_true]
      exact cell.symm.trans (all_append_boundaries rc t index empty frontier h _ (by omega))
    · rw [checked.staticFrontier l carry]
      by_cases lower : l.val<carryIndex index
      · simp only [computedFrontier,lower,true_or,if_true]
      · cases bit : index.testBit l.val <;>
          simp [computedFrontier,lower,carry,bit]

/-- The appended leaf is the same checked recipient/change pair, not an
unrelated expected output. This composes the earlier deterministic endpoint. -/
theorem same_output_pair_afterstate (rc : RoundConstants) (t : Table)
    (sequence index nextIndex : Nat) (empty frontier nextFrontier : Nat → Digest)
    (nextRoot : Digest) (outputs : OutputPairResiduals rc t)
    (h : AppendResiduals rc t index empty frontier)
    (checked : AfterstateChecks t sequence index nextIndex empty frontier nextFrontier nextRoot) :
    nextIndex=sequence+1 ∧ nextIndex≤2^20 ∧
    nextRoot=computedAt rc index empty frontier (nodeHash rc (recipient t) (change t)) 20 ∧
    (∀ l : Fin 20,nextFrontier l.val=
      computedFrontier rc index empty frontier (nodeHash rc (recipient t) (change t)) l.val) := by
  have result:=entire_afterstate_forced rc t sequence index nextIndex empty frontier nextFrontier
    nextRoot h checked
  rwa [pair_digest_is_ordered_outputs rc t outputs] at result

/-- Public digest bindings tie the checked output-pair constructor and every
candidate afterstate component to the same independently supplied commitments.
The theorem does not infer caller/account authority from those digests. -/
theorem public_output_pair_afterstate (rc : RoundConstants) (t : Table)
    (sequence index nextIndex : Nat) (empty frontier nextFrontier : Nat → Digest)
    (nextRoot publicRecipient publicChange : Digest) (outputs : OutputPairResiduals rc t)
    (h : AppendResiduals rc t index empty frontier)
    (checked : AfterstateChecks t sequence index nextIndex empty frontier nextFrontier nextRoot)
    (recipientBinding : ∀ i : Fin 8,t 475 i.val-publicRecipient i=0)
    (changeBinding : ∀ i : Fin 8,t 523 i.val-publicChange i=0) :
    publicChange 7≠0 ∧
    twoOutputsFields publicRecipient publicChange=some (computedPair publicRecipient publicChange) ∧
    nextIndex=sequence+1 ∧ nextIndex≤2^20 ∧
    nextRoot=computedAt rc index empty frontier (nodeHash rc publicRecipient publicChange) 20 ∧
    (∀ l : Fin 20,nextFrontier l.val=
      computedFrontier rc index empty frontier (nodeHash rc publicRecipient publicChange) l.val) := by
  have pair:=public_output_pair_endpoint rc t outputs publicRecipient publicChange
    recipientBinding changeBinding
  have result:=entire_afterstate_forced rc t sequence index nextIndex empty frontier nextFrontier
    nextRoot h checked
  rw [pair.2.2] at result
  exact ⟨pair.1,pair.2.1,result⟩

theorem append_cells_in_shape (l : Fin 20) :
    544≤16*(34+l.val) ∧ 16*(34+l.val)+12<864 ∧
    539≤539+16*l.val ∧ 539+16*l.val≤843 := by omega

#print axioms carry_scan_bound
#print axioms carry_scan_spec
#print axioms right_pattern_is_untweaked
#print axioms ordered_append_children
#print axioms append_node_input
#print axioms append_parent_step
#print axioms all_append_boundaries
#print axioms entire_afterstate_forced
#print axioms same_output_pair_afterstate
#print axioms public_output_pair_afterstate
#print axioms append_cells_in_shape
end AspisV8.SelectedAppendAfterstate
