import NJE_AddValue
import NJE_Pow5Realization
import NJE_ExternalTotal
import NJE_InternalPacket
import NJA_PointStaging
import NJA_RoundCell

set_option autoImplicit false
noncomputable section
namespace NJE_RoundComposition
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K
abbrev State := Fin 16 → U32

def cell (x c : U32) : U32 := NJE_Pow5Packet.result (NJE_AddValue.add x c)

theorem cell_law (x c : U32) (hx : x.val<2147483647) (hc : c.val<2147483647) :
 NJA_RoundCell.reference x c=ok (cell x c) ∧
 (cell x c).val<2147483647 ∧
 ((cell x c).val:K)=R0P.poseidonPow5 ((x.val:K)+(c.val:K)) := by
 have a := NJE_AddValue.law x c hx hc
 have p := NJE_Pow5Realization.law (NJE_AddValue.add x c)
 refine ⟨?_,p.2.1,?_⟩
 · simp only [NJA_RoundCell.reference,a.1,bind_tc_ok,p.1,cell]
 · exact p.2.2.trans (congrArg R0P.poseidonPow5 a.2.2)

structure FullCut (input constants : State) (cells : Nat → State) : Prop where
 start : cells 0=input
 next : ∀ (n : Nat) (h : n<16), ∀ k,
   cells (n+1) k=if k=⟨n,h⟩ then cell (cells n ⟨n,h⟩) (constants ⟨n,h⟩) else cells n k

theorem full_cells (input constants : State) (states : Nat → State)
 (cut : FullCut input constants states)
 (canonical : ∀ i, (input i).val<2147483647)
 (constants_domain : ∀ i, (constants i).val<2147483647) :
 ∀ i, (states 16 i).val<2147483647 ∧
 ((states 16 i).val:K)=R0P.poseidonPow5 ((input i).val+(constants i).val) := by
 have complete := NJA_PointStaging.complete input (fun i x => cell x (constants i)) states cut.start cut.next
 rw [complete]
 intro i
 exact (cell_law (input i) (constants i) (canonical i) (constants_domain i)).2

theorem full_round (input constants : State) (states bs : Nat → State)
 (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (post : Nat → State)
 (canonical : ∀ i, (input i).val<2147483647)
 (constants_domain : ∀ i, (constants i).val<2147483647)
 (cut : FullCut input constants states)
 (linear : NJE_ExternalStages.Cut (states 16) bs sums args post) :
 ∀ i, (post 16 i).val<2147483647 ∧
 ((post 16 i).val:K)=R0P.poseidonFullRound (fun j => ((input j).val:K))
   (fun j => ((constants j).val:K)) i := by
 have cells := full_cells input constants states cut canonical constants_domain
 have layer := NJE_ExternalTotal.result (states 16) bs sums args post linear
 have converted : (fun i => ((states 16 i).val:K))=
     fun i => R0P.poseidonPow5 ((input i).val+(constants i).val) := funext (fun i => (cells i).2)
 intro i
 exact ⟨(layer.2 i).1,by rw [(layer.2 i).2,converted];rfl⟩

#print cell_law
#print axioms cell_law
#print full_cells
#print axioms full_cells
#print full_round
#print axioms full_round
end NJE_RoundComposition
end
