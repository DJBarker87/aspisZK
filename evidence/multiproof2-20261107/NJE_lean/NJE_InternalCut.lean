import NJE_Residue
import NJA_InternalReduce
import NJA_PointStaging

set_option autoImplicit false
noncomputable section
namespace NJE_InternalCut
open Aeneas Aeneas.Std Result
open NJA_Internal

-- Transcribes NJA_internal_zero and NJA_internal_cell's selected-argument and
-- complete one-write/frame assertions, after the SAME full_sum was captured.
-- `part` must be supplied by a proved sum stage, never by an endpoint premise.
structure Cut (input : State) (part full : Nat) (args : Fin 16 → Nat)
    (steps : Nat → State) : Prop where
 start : steps 0=input
 full_value : full=part+(input 0).val
 zero_arg : args 0=part+2147483647-(input 0).val
 tail_arg : ∀ i, (nonzero : i.val≠0) →
   args i=full+(steps i.val i).val*2^(R0P.poseidonInternalShifts ⟨i.val-1,by omega⟩)
 next : ∀ (n : Nat) (h : n<16), ∀ k,
   steps (n+1) k=if k=⟨n,h⟩ then NJE_Residue.word (args ⟨n,h⟩) else steps n k

theorem unread (input : State) (part full : Nat) (args : Fin 16 → Nat)
    (steps : Nat → State) (cut : Cut input part full args steps) (i : Fin 16) :
    steps i.val i=input i := by
 have h := NJA_PointStaging.replay input (fun j _ => NJE_Residue.word (args j))
   steps cut.start cut.next i.val (Nat.le_of_lt i.isLt)
 rw [h]
 exact NJA_PointFrame.frame input _ i.val (Nat.le_of_lt i.isLt) i (by omega)

theorem args_source (input : State) (part full : Nat) (args : Fin 16 → Nat)
    (steps : Nat → State) (cut : Cut input part full args steps)
    (part_source : part=NJA_Internal.part input) (i : Fin 16) :
    args i=NJA_InternalReduce.argument input i := by
 by_cases hi : i.val=0
 · have eq : i=0 := Fin.ext hi
   subst i
   simpa [NJA_InternalReduce.argument,zeroArg,part_source] using cut.zero_arg
 · rw [cut.tail_arg i hi,unread input part full args steps cut i,cut.full_value,part_source]
   simp [NJA_InternalReduce.argument,hi,nonzeroArg]

theorem frame_result (input : State) (part full : Nat) (args : Fin 16 → Nat)
    (steps : Nat → State) (cut : Cut input part full args steps) :
    steps 16=fun i => NJE_Residue.word (args i) :=
 NJA_PointStaging.complete input (fun i _ => NJE_Residue.word (args i)) steps cut.start cut.next

#print unread
#print axioms unread
#print args_source
#print axioms args_source
#print frame_result
#print axioms frame_result
end NJE_InternalCut
end
