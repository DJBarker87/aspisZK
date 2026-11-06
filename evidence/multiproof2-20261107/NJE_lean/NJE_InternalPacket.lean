import NJE_InternalCut
import NJE_SumStage
import NJA_Mat4Cut

set_option autoImplicit false
noncomputable section
namespace NJE_InternalPacket
open Aeneas Aeneas.Std Result
open NJA_Internal

-- Both hypotheses are reviewed one-step native cut transcriptions. The sum
-- endpoint, untouched input cells, full_sum, and field laws are derived below.
theorem result (input : State) (sums : Nat → Nat) (full : Nat)
    (args : Fin 16 → Nat) (steps : Nat → State)
    (canonical : ∀ i, (input i).val<2147483647)
    (sum_cut : NJE_SumStage.Cut input sums)
    (cut : NJE_InternalCut.Cut input (sums 15) full args steps) :
    (∀ i, args i<2^62) ∧
    (∀ i, (steps 16 i).val<2147483647 ∧
      ((steps 16 i).val:K)=R0P.poseidonInternalLinear (fun j => ((input j).val:K)) i) := by
 have part := NJE_SumStage.complete input sums sum_cut
 have args_source := NJE_InternalCut.args_source input (sums 15) full args steps cut part
 constructor
 · intro i
   rw [args_source]
   exact NJA_InternalReduce.argument_bound input i canonical
 · rw [NJE_InternalCut.frame_result input (sums 15) full args steps cut]
   intro i
   have hz := NJA_Mat4Cut.reduction_determined (NJA_InternalReduce.word input i)
     (NJE_Residue.word (args i)) (by
       rw [NJE_Residue.value,NJA_InternalReduce.word_value input i canonical,args_source])
   obtain ⟨z,hz',cz,vz⟩ := NJA_InternalReduce.callee input i canonical
   have eq : z=NJE_Residue.word (args i) := Result.ok.inj (hz'.symm.trans hz)
   exact ⟨by simpa [eq] using cz,by simpa [eq] using vz⟩

#print result
#print axioms result
end NJE_InternalPacket
end
