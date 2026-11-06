import NLH_CompTailFold
import NLH_CompRun
import NLH_TermCompositionFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompRoot
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
abbrev Outcome := Result (core.result.Result State NLH_CompositionState.Error)
def Canonical : Outcome → Prop
 | .ok (.Ok st) => Canon st.composition ∧ canonical st.openings.z ∧ canonical st.mask ∧ Canon st.g ∧ Canon st.h ∧ Canon st.copy.active
 | _ => True
def projected (r : Outcome) := do let out ← r;ok (NLH_CompRun.project out)
theorem order_eq : NLH_CompositionState.order=.amount::.validate::NLH_CompTailFold.order := by
 simp only [NLH_CompositionState.order,NLH_CompTailFold.order,NLH_CompTailFold.headOrder,
   NLH_CompTailFold.loopOrder,List.append_assoc,List.cons_append,List.nil_append]
theorem amount_step (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) :
 step pub claims point lambda chi theta .amount st=
 if NLH_TermAmount.invalid pub.withdrawal_amount then ok (.Err .InvalidPublicAmount) else ok (.Ok st) := by
 cases h : pub.withdrawal_amount with
 | none => simp only [step,h,NLH_TermAmount.invalid,Bool.false_eq_true,ite_false]
 | some a =>
   by_cases bad : a=0#u32 ∨ 1073741824 ≤ a.val
   · simp only [step,h,NLH_TermAmount.invalid,if_pos bad,bad,decide_true,ite_true]
   · simp only [step,h,NLH_TermAmount.invalid,if_neg bad,bad,decide_false,Bool.false_eq_true,ite_false]
theorem factor_good (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (good : NLH_TermAmount.invalid pub.withdrawal_amount=false) :
 composition_parts pub claims point lambda chi theta=
 (do let r ← validate_transition pub
     match r with
     | .Err err => ok (.Err err)
     | .Ok _ => NLH_TermComposeTail.run pub claims point lambda chi theta) := by
 rw [NLH_TermCompositionFactor.source]
 unfold NLH_TermCompositionFactor.reference
 rw [NLH_TermAmount.source,bind_tc_ok]
 simp only [Aeneas.Std.uncurry,good,Bool.false_eq_true,ite_false]
 rfl
/-- Packaging only; not a row root and no native-cut producer. -/
theorem package (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (out : Outcome) (log : List Event)
 (cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial out log)
 (value : projected out=composition_parts pub claims point lambda chi theta) (canon : Canonical out) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial result events ∧
 events <+: NLH_CompositionState.order ∧ Canonical result ∧
 projected result=composition_parts pub claims point lambda chi theta ∧
 NLH_CompRun.reference pub claims point lambda chi theta=composition_parts pub claims point lambda chi theta := by
 refine ⟨out,log,cuts,NLH_RustCuts.attempted_prefix cuts,canon,value,?_⟩
 unfold NLH_CompRun.reference
 rw [NLH_RustCuts.result cuts]
 exact value
/-- Full237 Result and exact error/abort prefixes. Every child outcome is
internally instantiated; there is no accepted-only or endpoint hypothesis. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (hd : NKR_DigestChildren.Domain pub) (hc : canonical claims)
 (hp : canonical point) (hl : Canon lambda) (hchi : Canon chi) (ht : Canon theta)
 (asset : pub.asset_id.val < 2147483647) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial result events ∧
 events <+: NLH_CompositionState.order ∧ Canonical result ∧
 projected result=composition_parts pub claims point lambda chi theta ∧
 NLH_CompRun.reference pub claims point lambda chi theta=composition_parts pub claims point lambda chi theta := by
 cases bad : NLH_TermAmount.invalid pub.withdrawal_amount with
 | true =>
   have amount : step pub claims point lambda chi theta .amount NLH_CompRun.initial=ok (.Err .InvalidPublicAmount) := by
     rw [amount_step,bad];rfl
   have cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial
       (ok (.Err .InvalidPublicAmount)) [.amount] := by
     rw [order_eq];exact .returned amount
   apply package pub claims point lambda chi theta _ _ cuts
   · exact (NLH_TermAmount.rejected pub claims point lambda chi theta bad).symm
   · trivial
 | false =>
   have amount : step pub claims point lambda chi theta .amount NLH_CompRun.initial=ok (.Ok NLH_CompRun.initial) := by
     rw [amount_step,bad];rfl
   have factor := factor_good pub claims point lambda chi theta bad
   cases validation : validate_transition pub with
   | fail err =>
     have cut : step pub claims point lambda chi theta .validate NLH_CompRun.initial=fail err := by
       simp only [step,validation,bind_tc_fail]
     have cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial
         (fail err) [.amount,.validate] := by rw [order_eq];exact .next amount (.failed cut)
     apply package pub claims point lambda chi theta _ _ cuts
     · rw [factor,validation];rfl
     · trivial
   | div =>
     have cut : step pub claims point lambda chi theta .validate NLH_CompRun.initial=div := by
       simp only [step,validation,bind_tc_div]
     have cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial
         div [.amount,.validate] := by rw [order_eq];exact .next amount (.diverged cut)
     apply package pub claims point lambda chi theta _ _ cuts
     · rw [factor,validation];rfl
     · trivial
   | ok r =>
     cases r with
     | Err err =>
       have cut : step pub claims point lambda chi theta .validate NLH_CompRun.initial=ok (.Err err) := by
         simp only [step,validation,bind_tc_ok]
       have cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial
           (ok (.Err err)) [.amount,.validate] := by rw [order_eq];exact .next amount (.returned cut)
       apply package pub claims point lambda chi theta _ _ cuts
       · rw [factor,validation];rfl
       · trivial
     | Ok unit =>
       have cut : step pub claims point lambda chi theta .validate NLH_CompRun.initial=ok (.Ok NLH_CompRun.initial) := by
         simp only [step,validation,bind_tc_ok]
       obtain ⟨final,tail,tailCall,cc,cz,cm,cg,ch,ca⟩ := NLH_CompTailFold.source pub claims point lambda chi theta NLH_CompRun.initial
         hd hc hp hl hchi ht asset (NLH_TermAmount.canonical pub bad)
       have cuts : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) NLH_CompositionState.order NLH_CompRun.initial
           (ok (.Ok final)) (.amount::.validate::NLH_CompTailFold.order) := by
         rw [order_eq];exact .next amount (.next cut tail)
       apply package pub claims point lambda chi theta _ _ cuts
       · rw [factor,validation,bind_tc_ok,tailCall];rfl
       · exact ⟨cc,cz,cm,cg,ch,ca⟩
#print axioms order_eq
#print axioms amount_step
#print axioms factor_good
#print axioms package
#print source
#print axioms source
end AspisR1.NLH_CompRoot
end
