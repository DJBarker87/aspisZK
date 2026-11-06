import NJE_InternalRound
import NJE_ConstantsInitial
import NJE_ConstantsInternal
import NJE_ConstantsFinal
import NJE_PermutationFold
import NJA_TraceModel

set_option autoImplicit false
noncomputable section
namespace NJE_RoundTrace
open Aeneas Aeneas.Std Result
abbrev State := NJE_RoundComposition.State
abbrev K := NJA_Matrix.K
def cast (s : State) : Fin 16 → K := fun i => ((s i).val:K)
def Canonical (s : State) : Prop := ∀ i, (s i).val<2147483647

def Full (pre constants post : State) : Prop :=
 ∃ states bs sums args steps,
   NJE_RoundComposition.FullCut pre constants states ∧
   NJE_ExternalStages.Cut (states 16) bs sums args steps ∧ post=steps 16

def Internal (pre : State) (constant : U32) (post : State) : Prop :=
 ∃ sums full args steps,
   NJE_SumStage.Cut (NJE_InternalRound.nonlinear pre constant) sums ∧
   NJE_InternalCut.Cut (NJE_InternalRound.nonlinear pre constant) (sums 15) full args steps ∧
   post=steps 16

def Witness (pre post : State) (r : Fin 22) : Prop :=
 if h : r.val<4 then Full pre (NJE_ConstantsInitial.source ⟨r.val,h⟩) post
 else if h' : r.val<4+14 then
   Internal pre (NJE_ConstantsInternal.source ⟨r.val-4,by omega⟩) post
 else Full pre (NJE_ConstantsFinal.source ⟨r.val-4-14,by omega⟩) post

theorem one (pre post : State) (r : Fin 22) (canonical : Canonical pre)
 (cut : Witness pre post r) : Canonical post ∧ cast post=R0P.poseidonApplyRound r (cast pre) := by
 by_cases first : r.val<4
 · simp only [Witness,dif_pos first] at cut
   obtain ⟨states,bs,sums,args,steps,cells,linear,rfl⟩ := cut
   have law := NJE_RoundComposition.full_round pre (NJE_ConstantsInitial.source ⟨r.val,first⟩)
     states bs sums args steps canonical (NJE_ConstantsInitial.canonical _) cells linear
   refine ⟨fun i => (law i).1,?_⟩
   funext i
   dsimp only [cast]
   simpa only [R0P.poseidonApplyRound,dif_pos first,NJE_ConstantsInitial.model] using (law i).2
 · by_cases middle : r.val<4+14
   · simp only [Witness,dif_neg first,dif_pos middle] at cut
     obtain ⟨sums,full,args,steps,sum_cut,linear,rfl⟩ := cut
     have law := NJE_InternalRound.result pre (NJE_ConstantsInternal.source ⟨r.val-4,by omega⟩)
       sums full args steps canonical (NJE_ConstantsInternal.canonical _) sum_cut linear
     refine ⟨fun i => (law i).1,?_⟩
     funext i
     dsimp only [cast]
     simpa only [R0P.poseidonApplyRound,dif_neg first,dif_pos middle,
       NJE_ConstantsInternal.model] using (law i).2
   · simp only [Witness,dif_neg first,dif_neg middle] at cut
     obtain ⟨states,bs,sums,args,steps,cells,linear,rfl⟩ := cut
     have law := NJE_RoundComposition.full_round pre (NJE_ConstantsFinal.source ⟨r.val-4-14,by omega⟩)
       states bs sums args steps canonical (NJE_ConstantsFinal.canonical _) cells linear
     refine ⟨fun i => (law i).1,?_⟩
     funext i
     dsimp only [cast]
     simpa only [R0P.poseidonApplyRound,dif_neg first,dif_neg middle,
       NJE_ConstantsFinal.model] using (law i).2

-- Lean side of the staged-cut composition. NOT a row admission: an actual
-- frozen controller/callback-to-Witness association is still required.
theorem facts (input : State) (states : Fin 23 → State)
 (bs : Nat → State) (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat)
 (leading : Nat → State) (start : states 0=leading 16)
 (initial_cut : NJE_ExternalStages.Cut input bs sums args leading)
 (rounds : ∀ r, Witness (states r.castSucc) (states r.succ) r) :
 (∀ i : Fin 23, Canonical (states i)) ∧
 (∀ r, cast (states r.succ)=R0P.poseidonApplyRound r (cast (states r.castSucc))) ∧
 cast (states 0)=R0P.poseidonExternalLinear (cast input) := by
 have first := NJE_ExternalTotal.result input bs sums args leading initial_cut
 have initial : Canonical (states 0) := by rw [start];exact fun i => (first.2 i).1
 have canonical : ∀ i : Fin 23, Canonical (states i) := by
   intro i
   induction i using Fin.induction with
   | zero => exact initial
   | succ i ih => exact (one _ _ i ih (rounds i)).1
 have steps : ∀ r, cast (states r.succ)=R0P.poseidonApplyRound r (cast (states r.castSucc)) :=
   fun r => (one _ _ r (canonical _) (rounds r)).2
 have initial_value : cast (states 0)=R0P.poseidonExternalLinear (cast input) := by
   rw [start]
   funext i
   exact (first.2 i).2
 exact ⟨canonical,steps,initial_value⟩

theorem composition (input : State) (states : Fin 23 → State)
 (bs : Nat → State) (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat)
 (leading : Nat → State) (start : states 0=leading 16)
 (initial_cut : NJE_ExternalStages.Cut input bs sums args leading)
 (rounds : ∀ r, Witness (states r.castSucc) (states r.succ) r) :
 Canonical (states (Fin.last 22)) ∧
 cast (states (Fin.last 22))=R0P.poseidonPermutation (cast input) := by
 obtain ⟨canonical,steps,initial_value⟩ := facts input states bs sums args leading start initial_cut rounds
 have joined := NJE_PermutationFold.compose (fun i => cast (states i))
   (fun r => R0P.poseidonApplyRound r) steps
 have map : List.ofFn (fun r : Fin 22 => R0P.poseidonApplyRound (K:=K) r)=
     (List.ofFn (fun r : Fin 22 => r)).map (fun r => R0P.poseidonApplyRound r) := by
   rw [List.map_ofFn]
   rfl
 rw [map,List.foldl_map,initial_value] at joined
 exact ⟨canonical _,joined.symm.trans (NJE_PermutationFold.folded (cast input))⟩

def observed (input : State) (states : Fin 23 → State) (r : Fin 22) : NJA_Trace.Event State :=
 ⟨r.val,NJA_Trace.kind r.val,if r.val=0 then input else states r.castSucc,states r.succ⟩

theorem trace_values (input : State) (states : Fin 23 → State)
 (bs : Nat → State) (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat)
 (leading : Nat → State) (start : states 0=leading 16)
 (initial_cut : NJE_ExternalStages.Cut input bs sums args leading)
 (rounds : ∀ r, Witness (states r.castSucc) (states r.succ) r) :
 (List.ofFn (observed input states)).length=22 ∧
 ∀ r : Fin 22,
   (observed input states r).round=r.val ∧
   R0P.poseidonRoundKind r.val=some (NJA_TraceModel.kind (observed input states r).kind) ∧
   cast (observed input states r).input=(if r.val=0 then cast input else cast (states r.castSucc)) ∧
   cast (observed input states r).output=R0P.poseidonApplyRound r (cast (states r.castSucc)) := by
 obtain ⟨canonical,steps,initial_value⟩ := facts input states bs sums args leading start initial_cut rounds
 refine ⟨by simp,?_⟩
 intro r
 refine ⟨rfl,NJA_TraceModel.descriptor r.val r.isLt,?_,steps r⟩
 by_cases first : r.val=0 <;> simp [observed,first]

#print facts
#print axioms facts
#print trace_values
#print axioms trace_values
#print one
#print axioms one
#print composition
#print axioms composition
end NJE_RoundTrace
end
