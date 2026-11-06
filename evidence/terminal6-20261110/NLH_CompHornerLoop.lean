import NKI_InitialPrefix
import NLH_CompHornerStep
import NLH_RustCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompHornerLoop
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public)
/-- RuleB induction: one native arbitrary-prestate iteration at each event,
with exact prepared cache, current accumulator and head of the SAME iterator. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (events : List Event) (st : State)
 (shape : ∀ e∈events,∃ i,e=Event.horner i) (length : events.length=st.remaining.length)
 (ht : Canon theta) (hc : Canon st.composition) (hr : ∀ x∈st.remaining,Canon x)
 (hp : NJB_PreparedLaws.Domain st.prepared theta) :
 ∃ out,NLH_RustCuts.Cuts (step pub claims point lambda chi theta) events st
   (ok (.Ok {st with composition := out,remaining := []})) events ∧
 Canon out ∧ NLH_TermHornerCut.Trace st.prepared st.remaining st.composition out := by
 induction events generalizing st with
 | nil =>
   have empty : st.remaining=[] := List.length_eq_zero.mp (by omega)
   have same : {st with composition := st.composition,remaining := []}=st := by rw [←empty]
   refine ⟨st.composition,?_,hc,?_⟩
   · rw [same];exact .nil st
   · rw [empty];exact .nil _
 | cons e es ih =>
   obtain ⟨i,rfl⟩ := shape e (by simp)
   cases remaining : st.remaining with
   | nil => simp only [remaining,List.length_nil,List.length_cons] at length;omega
   | cons lane rest =>
     have laneCanonical : Canon lane := hr lane (by rw [remaining];simp)
     have restCanonical : ∀ x∈rest,Canon x := by
       intro x h;apply hr x;rw [remaining];simp only [List.mem_cons];exact Or.inr h
     obtain ⟨product,middle,pm,ma,window,cm,cut⟩ := NLH_CompHornerStep.source pub claims point lambda chi theta st i lane rest remaining ht hc laneCanonical hp
     let next : State := {st with composition := middle,remaining := rest}
     have tailLength : es.length=next.remaining.length := by
       change es.length=rest.length
       rw [remaining] at length
       simp only [List.length_cons] at length
       omega
     obtain ⟨out,tail,co,trace⟩ := ih next (fun e he => shape e (by simp only [List.mem_cons];exact Or.inr he)) tailLength cm restCanonical hp
     refine ⟨out,.next window tail,co,?_⟩
     rw [remaining]
     exact .cons pm ma cut trace
#print axioms source
end AspisR1.NLH_CompHornerLoop
end
