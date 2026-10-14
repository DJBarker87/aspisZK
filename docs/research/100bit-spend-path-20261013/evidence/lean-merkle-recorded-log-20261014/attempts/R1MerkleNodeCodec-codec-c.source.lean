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
  let idx := child.val * 32 + byte.val
  have hidx : idx < 256 := by dsimp [idx]; omega
  have hpos : 1 + child.val * 32 + byte.val = idx + 1 := by
    dsimp [idx]
    omega
  have hdiv : idx / 32 = child.val := by dsimp [idx]; omega
  have hmod : idx % 32 = byte.val := by dsimp [idx]; omega
  change ((0x18 : Byte) :: List.ofFn (childByte cs))[1 + child.val * 32 + byte.val]?.getD 0 =
    cs child byte
  rw [hpos, List.getElem?_cons_succ]
  simp only [List.getElem?_ofFn, if_pos hidx, Option.getD_some]
  simp [childByte, idx, hdiv, hmod]

theorem parse_nodeInput (cs : Children) : parse (nodeInput cs) = some cs := by
  simp [parse, readChildren_nodeInput]

theorem parse_sound {input : List Byte} {cs : Children}
    (h : parse input = some cs) : nodeInput cs = input := by
  unfold parse at h
  dsimp only at h
  by_cases hguard : nodeInput (readChildren input) = input
  · simp [hguard] at h
    subst cs
    exact hguard
  · simp [hguard] at h

#print axioms readChildren_nodeInput
#print axioms parse_nodeInput
#print axioms parse_sound

end AspisR1.MerkleNodeCodec
