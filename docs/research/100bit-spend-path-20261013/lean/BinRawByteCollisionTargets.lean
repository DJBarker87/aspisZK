import AllAddressCollisionTrace
import BinMerkleNodeCodec
import RawByteCollisionTargets

/-! The five binary collision targets on literal, unrestricted byte strings.
These are two strict binary-child parsers, the trailing and
offset-38 commitment-root readers, and the leading duplex state. No bound
on adversarial input length and no padded address encoding is used by the
event or its probability law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinRawByteCollisionTargets

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.UniformStateFirstHit

def fixed (offset : Nat) (input : Bytes) : Option State :=
  if offset + 32 ≤ input.length then
    some (stateOfBytes (input.drop offset)) else none

def trailing (input : Bytes) : Option State :=
  if 32 ≤ input.length then
    some (stateOfBytes (input.drop (input.length - 32))) else none

def child (j : Fin 2) (input : Bytes) : Option State :=
  (BinMerkleNodeCodec.parse input).map fun cs => cs j

def pred (j : Fin 5) (input : Bytes) : Option State :=
  if h : j.val < 2 then child ⟨j.val, h⟩ input
  else if j.val = 2 then trailing input
  else if j.val = 3 then fixed 38 input
  else fixed 0 input

theorem pred_child (j : Fin 2) (input : Bytes) :
    pred ⟨j.val, by omega⟩ input = child j input := by
  simp only [pred, dif_pos j.isLt]

theorem pred_tail (input : Bytes) : pred 2 input = trailing input := by
  simp [pred]

theorem pred_middle (input : Bytes) : pred 3 input = fixed 38 input := by
  simp [pred]

theorem pred_prefix (input : Bytes) : pred 4 input = fixed 0 input := by
  simp [pred]

theorem fixed_frame (offset : Nat) (pre : Bytes) (s : State) (tail : Bytes)
    (hpre : pre.length = offset) :
    fixed offset (pre ++ bytes s ++ tail) = some s := by
  have hfit : offset + 32 ≤ (pre ++ bytes s ++ tail).length := by
    simp only [List.length_append, bytes_length, hpre]
    omega
  have hdrop : (pre ++ bytes s ++ tail).drop offset = bytes s ++ tail := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [fixed, if_pos hfit, hdrop, stateOfBytes_bytes]

theorem trailing_frame (pre : Bytes) (s : State) :
    trailing (pre ++ bytes s) = some s := by
  have hlen : (pre ++ bytes s).length = pre.length + 32 := by
    simp [bytes_length]
  have hfit : 32 ≤ (pre ++ bytes s).length := by rw [hlen]; omega
  rw [trailing, if_pos hfit, hlen, Nat.add_sub_cancel_right]
  rw [List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
    List.nil_append]
  simpa using congrArg some (stateOfBytes_bytes s ([] : Bytes))

theorem prefix_of_take (input : Bytes) (s : State)
    (htake : input.take 32 = bytes s) : fixed 0 input = some s := by
  have he : input = bytes s ++ input.drop 32 := by
    rw [← htake]
    exact (List.take_append_drop 32 input).symm
  rw [he]
  simpa using fixed_frame 0 ([] : Bytes) s (input.drop 32) rfl

theorem child_node (cs : BinMerkle32Path.Children) (j : Fin 2) :
    child j (BinMerkle32Path.nodeInput cs) = some (cs j) := by
  simp only [child, BinMerkleNodeCodec.parse_nodeInput, Option.map_some]

def event {O : Type} (iv : State) (Q : Nat) (v : View Bytes State O) : Prop :=
  hitsBad (AllAddressCollision.bad iv pred Q) emptyTable v.1

theorem mass {O : Type} (iv : State) (Q : Nat) (p : Program Bytes State O)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable (eval H p).1 ≤ Q) :
    lazyMean p emptyTable (fun v => indicator (event iv Q v)) ≤
      6 * (Q : ℚ)^2 / (256^32 : ℚ) := by
  have h := AllAddressCollision.mass iv pred Q p hQ
  rw [state_card] at h
  calc
    _ ≤ ((5 : ℚ) + 1) * (Q : ℚ)^2 / (256^32 : ℚ) := by
      simpa only [event, Nat.cast_pow, Nat.cast_ofNat] using h
    _ = 6 * (Q : ℚ)^2 / (256^32 : ℚ) := by ring

/-- A parsed Merkle child output must already have been read before the node. -/
theorem child_before_node (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv pred Q) emptyTable tr)
    (cs : BinMerkle32Path.Children) (j : Fin 2) (a : Bytes)
    (ha : Read tr a) (hnode : Read tr (BinMerkle32Path.nodeInput cs))
    (he : H a = cs j) : Before tr a (BinMerkle32Path.nodeInput cs) := by
  apply AllAddressCollisionTrace.parsed_target_after iv pred H tr Q hcons hQ hout
    ⟨j.val, by omega⟩ a (BinMerkle32Path.nodeInput cs) ha hnode
  rw [pred_child, child_node, he]

/-- A trailing commitment root must precede the commitment frame's first read. -/
theorem root_before_trailing_frame (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv pred Q) emptyTable tr)
    (pre : Bytes) (a : Bytes) (ha : Read tr a)
    (hframe : Read tr (pre ++ bytes (H a))) :
    Before tr a (pre ++ bytes (H a)) := by
  apply AllAddressCollisionTrace.parsed_target_after iv pred H tr Q hcons hQ hout
    2 a (pre ++ bytes (H a)) ha hframe
  rw [pred_tail, trailing_frame]

/-- The folded-root offset-38 frame has the same chronological guarantee. -/
theorem root_before_middle_frame (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv pred Q) emptyTable tr)
    (pre tail : Bytes) (hpre : pre.length = 38) (a : Bytes) (ha : Read tr a)
    (hframe : Read tr (pre ++ bytes (H a) ++ tail)) :
    Before tr a (pre ++ bytes (H a) ++ tail) := by
  apply AllAddressCollisionTrace.parsed_target_after iv pred H tr Q hcons hQ hout
    3 a (pre ++ bytes (H a) ++ tail) ha hframe
  rw [pred_middle, fixed_frame 38 pre (H a) tail hpre]

theorem duplex_state_before_frame (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv pred Q) emptyTable tr)
    (a b : Bytes) (ha : Read tr a) (hb : Read tr b)
    (hpre : b.take 32 = bytes (H a)) : Before tr a b := by
  apply AllAddressCollisionTrace.parsed_target_after iv pred H tr Q hcons hQ hout
    4 a b ha hb
  rw [pred_prefix]
  exact prefix_of_take b (H a) hpre

#print axioms pred_child
#print axioms pred_tail
#print axioms pred_middle
#print axioms pred_prefix
#print axioms fixed_frame
#print axioms trailing_frame
#print axioms prefix_of_take
#print axioms child_node
#print axioms mass
#print axioms child_before_node
#print axioms root_before_trailing_frame
#print axioms root_before_middle_frame
#print axioms duplex_state_before_frame
end AspisR1.BinRawByteCollisionTargets
end
