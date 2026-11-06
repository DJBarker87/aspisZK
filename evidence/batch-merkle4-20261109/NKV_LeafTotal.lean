import NKV_LeafHistory
import MultiproofConeSlotState
set_option autoImplicit false
noncomputable section
namespace NKV_LeafTotal
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- Every admitted full leaf prefix returns, rejecting duplicates included.
An arbitrary child-success or a successful whole fold is not a premise. -/
theorem source (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s : reference.Scratch)
 (room : s.n.val+positions.length≤16) :
 ∃ out,(NKV_LeafBuild.build H p q kind positions s).2=ok out := by
 obtain ⟨out,chain⟩:=NKL_LeafTotal.total (NKV_LeafBuild.leaves H p q kind positions) s
   (by simpa only [NKV_LeafBuild.leaves,List.length_map] using room)
 have total : NKV_StepErasure.mapResult NKV_LeafBuild.forget (NKV_LeafBuild.build H p q kind positions s).2=ok out := by
   rw [NKV_LeafBuild.fold]
   exact NKB_LeafChain.source _ _ _ chain
 cases run : (NKV_LeafBuild.build H p q kind positions s).2 with
 | fail e => rw [run] at total;cases total
 | div => rw [run] at total;cases total
 | ok answer => exact ⟨answer,rfl⟩

/-- Same initial reset used in the adopted slot model; caller bounds are
computed from the actual sorted list, including TX2's twelve positions. -/
theorem reset (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (s : reference.Scratch) :
 ∃ out,(NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
   (MultiproofConeSlotState.reset s)).2=ok out := by
 apply source
 have len:=MultiproofConeLeafFrozen.sorted_length q batch kind
 change 0+_≤16
 omega

set_option pp.proofs false
#print source
#print reset
#print axioms source
#print axioms reset
end NKV_LeafTotal
end
