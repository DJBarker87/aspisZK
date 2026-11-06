import NJE_RoundComposition

set_option autoImplicit false
noncomputable section
namespace NJE_InternalRound
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K
abbrev State := NJE_RoundComposition.State

def nonlinear (input : State) (constant : U32) : State :=
 fun i => if i=0 then NJE_RoundComposition.cell (input 0) constant else input i

theorem nonlinear_value (input : State) (constant : U32)
 (canonical : ∀ i, (input i).val<2147483647) (hc : constant.val<2147483647) :
 (∀ i, (nonlinear input constant i).val<2147483647) ∧
 (fun i => ((nonlinear input constant i).val:K))=
   fun i => if i=0 then R0P.poseidonPow5 (((input 0).val:K)+(constant.val:K)) else ((input i).val:K) := by
 have value := NJE_RoundComposition.cell_law (input 0) constant (canonical 0) hc
 constructor
 · intro i
   by_cases zero : i=0
   · simpa [nonlinear,zero] using value.2.1
   · simpa [nonlinear,zero] using canonical i
 · funext i
   by_cases zero : i=0
   · simpa [nonlinear,zero] using value.2.2
   · simp [nonlinear,zero]

-- Native NJA_internal_round_cell installs this one selected write; the emitted
-- cell law above supplies the raw log's replies, rather than a child-law premise.
theorem result (input : State) (constant : U32) (sums : Nat → Nat) (full : Nat)
 (args : Fin 16 → Nat) (post : Nat → State)
 (canonical : ∀ i, (input i).val<2147483647) (hc : constant.val<2147483647)
 (sum_cut : NJE_SumStage.Cut (nonlinear input constant) sums)
 (linear_cut : NJE_InternalCut.Cut (nonlinear input constant) (sums 15) full args post) :
 ∀ i, (post 16 i).val<2147483647 ∧
 ((post 16 i).val:K)=R0P.poseidonInternalRound (fun j => ((input j).val:K)) (constant.val:K) i := by
 have nonlinear_law := nonlinear_value input constant canonical hc
 have layer := NJE_InternalPacket.result (nonlinear input constant) sums full args post
   nonlinear_law.1 sum_cut linear_cut
 intro i
 exact ⟨(layer.2 i).1,by rw [(layer.2 i).2,nonlinear_law.2];rfl⟩

#print nonlinear_value
#print axioms nonlinear_value
#print result
#print axioms result
end NJE_InternalRound
end
