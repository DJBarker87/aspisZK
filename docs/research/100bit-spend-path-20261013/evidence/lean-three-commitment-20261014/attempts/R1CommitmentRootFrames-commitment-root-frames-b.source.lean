import R1CommitmentRootTargets
import R1PublicInitFrame

/-! Literal byte-frame aliases for the three commitment-root target readers. -/
set_option autoImplicit false
namespace AspisR1.CommitmentRootFrames

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def c2Prefix (state : State) : Bytes := bytes state ++ [0, 0xa2, 1, 32, 0, 0, 0]

def c2Frame (state root : State) : Bytes := c2Prefix state ++ bytes root

theorem c2Prefix_length (state : State) : (c2Prefix state).length = 39 := by
  simp [c2Prefix, bytes_length]

theorem c2Frame_length (state root : State) : (c2Frame state root).length = 71 := by
  simp [c2Frame, c2Prefix_length, bytes_length]

def c2Addr {L : Nat} (state root : State) (hL : 71 ≤ L) : Addr L :=
  Addr.ofBytes (c2Frame state root) (by
    have hh : (c2Frame state root).length = 71 := c2Frame_length state root
    rw [hh]
    exact hL)

def foldedPrefix (state : State) : Bytes := bytes state ++ [0, 0xbe, 0, 1, 0, 0]

def foldedFrame (state root : State) (tail : Bytes) : Bytes :=
  foldedPrefix state ++ bytes root ++ tail

theorem foldedPrefix_length (state : State) : (foldedPrefix state).length = 38 := by
  simp [foldedPrefix, bytes_length]

theorem foldedFrame_length (state root : State) (tail : Bytes)
    (htail : tail.length = 224) : (foldedFrame state root tail).length = 294 := by
  simp [foldedFrame, foldedPrefix_length, bytes_length, htail]

def foldedAddr {L : Nat} (state root : State) (tail : Bytes)
    (htail : tail.length = 224) (hL : 294 ≤ L) : Addr L :=
  Addr.ofBytes (foldedFrame state root tail) (by
    have hh : (foldedFrame state root tail).length = 294 := foldedFrame_length state root tail htail
    rw [hh]
    exact hL)


theorem pred_c1 {L : Nat} (pub : Bytes) (hL : 75 + pub.length ≤ L) (root : State) :
    CommitmentRootTargets.pred 0 (PublicInitFrame.addr pub hL root) = some root := by
  simpa [PublicInitFrame.addr, PublicInitFrame.frame, TrailingStateFrame.frame] using
    CommitmentRootTargets.pred_tail (PublicInitFrame.pre pub) root (by
      rw [PublicInitFrame.pre_length, bytes_length]
      omega)

theorem pred_c2 {L : Nat} (state root : State) (hL : 71 ≤ L) :
    CommitmentRootTargets.pred 0 (c2Addr state root hL) = some root := by
  simpa [CommitmentRootTargets.pred, c2Addr, c2Frame, TrailingStateFrame.frame] using
    TrailingStateFrame.tailState_frameAddr (c2Prefix state) root (by
      rw [c2Frame_length]
      exact hL)

theorem pred_folded {L : Nat} (state root : State) (tail : Bytes)
    (htail : tail.length = 224) (hL : 294 ≤ L) :
    CommitmentRootTargets.pred 1 (foldedAddr state root tail htail hL) = some root := by
  rw [foldedAddr]
  unfold CommitmentRootTargets.pred
  simp only [show (1 : Fin 2).val ≠ 0 by decide, ↓reduceIte]
  exact FixedOffsetTarget.parse_ofBytes 38 (foldedPrefix state) root tail
    (foldedPrefix_length state) (by
      have hh := foldedFrame_length state root tail htail
      rw [foldedFrame] at hh
      exact hh ▸ hL)

#print axioms c2Prefix_length
#print axioms c2Frame_length
#print axioms foldedPrefix_length
#print axioms foldedFrame_length
#print axioms pred_c1
#print axioms pred_c2
#print axioms pred_folded

end AspisR1.CommitmentRootFrames
