import R1Merkle32Path
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Lean.Elab.Tactic.Omega

/-! Constructive fixed-width reader and exact node-input re-encoding guard. -/
set_option autoImplicit false
namespace AspisR1.MerkleNodeCodec

open Merkle32Path

def readChildren (input : List Byte) : Children :=
  fun child byte => (input[1 + child.val * 32 + byte.val]?).getD 0

def parse (input : List Byte) : Option Children :=
  let cs := readChildren input
  if nodeInput cs = input then some cs else none

theorem readChildren_nodeInput (cs : Children) :
    readChildren (nodeInput cs) = cs := by
  funext child
  funext byte
  have hidx : child.val * 32 + byte.val < 256 := by omega
  have hdiv : (child.val * 32 + byte.val) / 32 = child.val := by omega
  have hmod : (child.val * 32 + byte.val) % 32 = byte.val := by omega
  simp [readChildren, nodeInput, nodeBytes, childByte, hidx, hdiv, hmod]

theorem parse_nodeInput (cs : Children) : parse (nodeInput cs) = some cs := by
  simp [parse, readChildren_nodeInput]

theorem parse_sound {input : List Byte} {cs : Children}
    (h : parse input = some cs) : nodeInput cs = input := by
  unfold parse at h
  split at h
  · injection h with hcs
    subst cs
    assumption
  · contradiction

#print axioms readChildren_nodeInput
#print axioms parse_nodeInput
#print axioms parse_sound

end AspisR1.MerkleNodeCodec
