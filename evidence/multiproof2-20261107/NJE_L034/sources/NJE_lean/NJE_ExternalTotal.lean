import NJE_ExternalStages

set_option autoImplicit false
noncomputable section
namespace NJE_ExternalTotal
open Aeneas Aeneas.Std Result NJA_ChunkFrame NJE_ExternalBlocks

theorem unread (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : NJE_ExternalStages.Cut input bs sums args steps) (i : Fin 16) :
    steps i.val i=bs 4 i := by
 rw [NJA_PointStaging.replay (bs 4) (fun i _ => NJE_Residue.word (args i)) steps cut.start cut.next
   i.val (Nat.le_of_lt i.isLt)]
 exact NJA_PointFrame.frame _ _ i.val (Nat.le_of_lt i.isLt) i (by omega)

theorem argument (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : NJE_ExternalStages.Cut input bs sums args steps) (i : Fin 16) :
    args i=NJA_External.arg (blocks input) i := by
 rw [cut.arguments i,unread input bs sums args steps cut i,
   NJE_ExternalStages.blocks_result input bs sums args steps cut,
   NJE_ExternalStages.sum_result input bs sums args steps cut]
 rfl

theorem result (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : NJE_ExternalStages.Cut input bs sums args steps) :
    (∀ i, args i<2^62) ∧
    (∀ i, (steps 16 i).val<2147483647 ∧
      ((steps 16 i).val:K)=R0P.poseidonExternalLinear (fun j => ((input j).val:K)) i) := by
 have args_eq := argument input bs sums args steps cut
 constructor
 · intro i
   rw [args_eq]
   exact NJA_External.arg_bound _ _
 · have frame : NJA_ExternalCut.Cut (blocks input) (NJE_ExternalPacket.events input) steps := by
     constructor
     · exact cut.start.trans (NJE_ExternalStages.blocks_result input bs sums args steps cut)
     · intro i;exact ⟨rfl,rfl,rfl⟩
     · intro n h k
       simpa only [NJE_ExternalPacket.events,args_eq] using cut.next n h k
   exact NJE_ExternalPacket.result input steps frame

#print unread
#print axioms unread
#print argument
#print axioms argument
#print result
#print axioms result
end NJE_ExternalTotal
end
