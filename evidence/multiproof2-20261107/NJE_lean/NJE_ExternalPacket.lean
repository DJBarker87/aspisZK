import NJE_ExternalBlocks
import NJA_ExternalCut
import NJA_Sums

set_option autoImplicit false
noncomputable section
namespace NJE_ExternalPacket
open Aeneas Aeneas.Std Result NJA_ChunkFrame
open NJE_ExternalBlocks
abbrev Event := NJA_Pow5Cut.Event

def events (input : State U32) (i : Fin 16) : Event :=
 ⟨1,NJA_External.arg (blocks input) i,0,
   NJE_Residue.word (NJA_External.arg (blocks input) i)⟩

theorem laws (input : State U32) : NJA_ExternalCut.CalleeLaws (events input) := by
 intro i; exact NJE_Residue.value _

theorem domains (input : State U32) (i : Fin 16) :
    (events input i).a<2^62 ∧ (events input i).out.val<2147483647 :=
 ⟨NJA_External.arg_bound _ _,NJE_Residue.canonical _⟩

-- The prior endpoint-valued `blocks` premise is discharged by the matrix packet.
-- This is a complete arithmetic/frame composition SUPPORT root; admission still
-- requires native control/source association for the external stage cut.
theorem result (input : State U32) (steps : Nat → State U32)
    (cut : NJA_ExternalCut.Cut (blocks input) (events input) steps) :
    ∀ i, (steps 16 i).val<2147483647 ∧
      ((steps 16 i).val:K)=R0P.poseidonExternalLinear (fun j => ((input j).val:K)) i :=
 NJA_ExternalCut.result input (blocks input) (events input) steps cut (laws input) (block_value input)

#print laws
#print axioms laws
#print domains
#print axioms domains
#print result
#print axioms result
end NJE_ExternalPacket
end
