import NKR_TermHorner
import NJB_PreparedLaws
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermHornerCut
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal
structure Observation where
 cache : NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32
 input : NQ
 left : NQ
 right : NQ
 out : NQ
 calls : Nat
/-- NKR_horner_step_cut exact2call native arbitrary-prestate record; the cache
is read-only and product/returned scalar replies are universally quantified. -/
def Cut (p : NP) (before lane product out : NQ) (ob : Observation) : Prop :=
 ob.cache=NJB_PreparedCarrier.words p ∧ ob.input=before ∧ ob.left=product ∧ ob.right=lane ∧ ob.out=out ∧ ob.calls=2

def observation (p : NP) (before lane product out : NQ) : Observation :=
 ⟨NJB_PreparedCarrier.words p,before,product,lane,out,2⟩

def step (p : NP) (before lane : NQ) : Result NQ := do
 let product←field.PreparedQm31Multiplier.mul p before
 field.QM31.add product lane

theorem step_source (p : NP) (theta before lane : NQ) (ht : Canon theta)
 (hb : Canon before) (hl : Canon lane) (hp : NJB_PreparedLaws.Domain p theta) :
 ∃ product out,field.PreparedQm31Multiplier.mul p before=ok product ∧
 field.QM31.add product lane=ok out ∧ step p before lane=ok out ∧ Canon out ∧
 Cut p before lane product out (observation p before lane product out) := by
 obtain ⟨product,pc,cp,_⟩:=NJB_PreparedLaws.mul_result p theta before ht hb hp
 obtain ⟨out,oc,co,_⟩:=NJB_StubLaws.qm_add product lane cp hl
 exact ⟨product,out,pc,oc,by simp only [step,pc,oc,bind_tc_ok],co,⟨rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

inductive Trace (p : NP) : List NQ → NQ → NQ → Prop
 | nil (before) : Trace p [] before before
 | cons {lane rest before product middle after} :
   field.PreparedQm31Multiplier.mul p before=ok product → field.QM31.add product lane=ok middle →
   Cut p before lane product middle (observation p before lane product middle) →
   Trace p rest middle after → Trace p (lane::rest) before after

/-- RuleB: the same native2call step chains by induction into BOTH actual
emitted reverse-loop carriers, preserving every intermediate canonical domain. -/
theorem loops_source (xs : List NQ) (p : NP) (theta before : NQ)
 (ht : Canon theta) (hb : Canon before) (hp : NJB_PreparedLaws.Domain p theta)
 (hc : ∀ x∈xs,Canon x) :
 ∃ out,Trace p xs before out ∧ Canon out ∧
 composition_parts_loop0 ⟨xs.reverse⟩ p before=ok out ∧
 composition_parts_loop1 ⟨xs.reverse⟩ p before=ok out := by
 induction xs generalizing before with
 | nil=>
   refine ⟨before,.nil before,hb,?_,?_⟩
   all_goals
    first | rw [composition_parts_loop0] | rw [composition_parts_loop1]
    simp only [List.reverse_nil,core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
     FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
     List.reverse_nil,bind_tc_ok]
    rfl
 | cons lane xs ih=>
   obtain ⟨product,middle,pm,ma,_,cm,cut⟩:=step_source p theta before lane ht hb (hc lane (by simp)) hp
   obtain ⟨out,tr,co,loop0,loop1⟩:=ih middle cm (fun x hx=>hc x (by simp only [List.mem_cons];exact Or.inr hx))
   refine ⟨out,.cons pm ma cut tr,co,?_,?_⟩
   · rw [composition_parts_loop0]
     simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      List.reverse_reverse,bind_tc_ok]
     change (do let product←field.PreparedQm31Multiplier.mul p before
                let middle←field.QM31.add product lane
                composition_parts_loop0 ⟨xs.reverse⟩ p middle)=ok out
     rw [pm,bind_tc_ok,ma,bind_tc_ok,loop0]
   · rw [composition_parts_loop1]
     simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      FIq_Native.core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      List.reverse_reverse,bind_tc_ok]
     change (do let product←field.PreparedQm31Multiplier.mul p before
                let middle←field.QM31.add product lane
                composition_parts_loop1 ⟨xs.reverse⟩ p middle)=ok out
     rw [pm,bind_tc_ok,ma,bind_tc_ok,loop1]

/-- The full23728step field/frame chain, with SAME constructor/cache at both
loops. All constructor/product domains are internally established. -/
theorem source (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize) (theta seed : NQ)
 (hs : canonical semantic) (hp : canonical poseidon) (ht : Canon theta) (hc : Canon seed) :
 ∃ p middle out,field.PreparedQm31Multiplier.new theta=ok p ∧ NJB_PreparedLaws.Domain p theta ∧
 Trace p semantic.val.reverse seed middle ∧ Trace p poseidon.val.reverse middle out ∧
 FIv_FoldsTotal.body semantic poseidon theta seed=ok out ∧ Canon out := by
 obtain ⟨p,pc,dp⟩:=NJB_PreparedLaws.new_result theta ht
 obtain ⟨middle,first,cm,l0,_⟩:=loops_source semantic.val.reverse p theta seed ht hc dp (fun x hx=>hs x (List.mem_reverse.mp hx))
 obtain ⟨out,second,co,_,l1⟩:=loops_source poseidon.val.reverse p theta middle ht cm dp (fun x hx=>hp x (List.mem_reverse.mp hx))
 simp only [List.reverse_reverse] at l0 l1
 refine ⟨p,middle,out,pc,dp,first,second,?_,co⟩
 simp only [FIv_FoldsTotal.body,pc,l0,l1,bind_tc_ok]
#print axioms step_source
#print axioms loops_source
#print source
#print axioms source
end AspisR1.NKR_TermHornerCut
end
