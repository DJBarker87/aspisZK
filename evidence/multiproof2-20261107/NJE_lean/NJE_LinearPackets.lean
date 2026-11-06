import NJE_ExternalTotal
import NJE_InternalPacket

set_option autoImplicit false
noncomputable section
namespace NJE_LinearPackets
open Aeneas Aeneas.Std Result
open NJA_ChunkFrame
abbrev K := NJA_Matrix.K

theorem TX1_303 (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : NJE_ExternalStages.Cut input bs sums args steps) :
    (∀ i, args i<2^62) ∧
    (∀ i, (steps 16 i).val<2147483647 ∧
      ((steps 16 i).val:K)=R0P.poseidonExternalLinear (fun j => ((input j).val:K)) i) := NJE_ExternalTotal.result input bs sums args steps cut

#print TX1_303
#print axioms TX1_303

theorem TX1_304 (input : NJA_Internal.State) (sums : Nat → Nat) (full : Nat)
    (args : Fin 16 → Nat) (steps : Nat → NJA_Internal.State)
    (canonical : ∀ i, (input i).val<2147483647)
    (sum_cut : NJE_SumStage.Cut input sums)
    (cut : NJE_InternalCut.Cut input (sums 15) full args steps) :
    (∀ i, args i<2^62) ∧
    (∀ i, (steps 16 i).val<2147483647 ∧
      ((steps 16 i).val:K)=R0P.poseidonInternalLinear (fun j => ((input j).val:K)) i) := NJE_InternalPacket.result input sums full args steps canonical sum_cut cut

#print TX1_304
#print axioms TX1_304
end NJE_LinearPackets
end
