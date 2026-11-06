import NIW_AlignFinishExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishInvocation
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishExecution Classical

def Clause (r : NP6_StdModel.Reservation) : Event → Prop
 | .round _ bytes alpha claim out => out=NHT_RoundPacket.packet bytes alpha claim
 | .new p out => out=FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z
 | .pair owner alpha message kappa out => out=NIG_PairExport.packet r owner alpha message kappa
 | .dot message weights out => out=NHQ_PacketPorts.dot message weights

theorem observe_all {A B : Type} (P : Event → Prop) (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B)
 (head : P (event call))
 (tail : ∀ value,call=ok (.Ok value) → ∀ e∈(next value).2,P e) :
 ∀ e∈(observe call event next).2,P e := by
 cases call with
 | fail err => intro e member;simp only [observe,List.mem_singleton] at member;subst e;exact head
 | div => intro e member;simp only [observe,List.mem_singleton] at member;subst e;exact head
 | ok reply =>
  cases reply with
  | Err err => intro e member;simp only [observe,List.mem_singleton] at member;subst e;exact head
  | Ok value =>
   simp only [observe,List.mem_cons]
   intro e member
   rcases member with same | later
   · subst e;exact head
   · exact tail value rfl e later

/-- Child clauses are produced, rather than retained as a root assumption.
Every outcome is the complete entered source call; observations stop on
Err/fail/div, including the same owned NEW result and pair arguments. -/
theorem clauses (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 ∀ event∈(run r v p a).2,Clause r event := by
 have ca0 := (NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)).2
 have ca1 := (NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)).2
 unfold run
 apply observe_all
 · exact (NHT_RoundPacket.source r v.round0 _ p.claim 0#usize ca0 (by decide)).symm
 intro first firstCall
 apply observe_all
 · exact (NHT_RoundPacket.source r v.round1 _ first 1#usize ca1 (by decide)).symm
 intro claim claimCall
 apply observe_all
 · exact NIG_FinishExport.NHM_new r p
 intro owner newCall
 cases range : core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice FE)) p.alpha {«end»:=2#usize} with
 | fail err => intro event member;cases member
 | div => intro event member;cases member
 | ok alpha =>
  apply observe_all
  · exact NIG_PairExport.source r owner alpha v.final_message p.kappa
  intro pair pairCall
  split
  · intro event member;cases member
  · apply observe_all
    · rfl
    intro actual dotCall event member
    cases member

#print axioms observe_all
#print axioms clauses
end AspisR1.NIW_AlignFinishInvocation
