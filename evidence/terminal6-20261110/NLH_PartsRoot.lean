import NLH_CompRoot
import NLH_PartsFold
import NLH_TermPartsFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsRoot
open Aeneas Aeneas.Std Result FIq_Native NLH_PartsState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
abbrev Outcome := Result (core.result.Result State NKR_TermTail.Error)
def initial : State := ⟨(field.QM31.ZERO,NLH_CompRun.zeros 16#usize,NLH_CompRun.zeros 10#usize,
 field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO),(fun _ => field.QM31.ZERO)⟩
def project : core.result.Result State NKR_TermTail.Error → core.result.Result NKR_TermTail.Output NKR_TermTail.Error
 | .Err e => .Err e
 | .Ok st => .Ok (returned st)
def projected (r : Outcome) := do let out ← r;ok (project out)
def Canonical : Outcome → Prop
 | .ok (.Ok st) => Canon (st.locals 8) ∧ canonical st.child.2.1 ∧ canonical st.child.2.2.1 ∧ Canon st.child.2.2.2.1
 | _ => True
def reference (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) := do
 let r ← NLH_FoldRust.run (step pub claims point zc lambda chi theta mu) order initial
 ok (project r)
theorem package (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (out : Outcome) (log : List Event)
 (cuts : NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial out log)
 (value : projected out=terminal_parts pub claims point lambda chi theta zc mu) (canon : Canonical out) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial result events ∧
 events <+: order ∧ Canonical result ∧ projected result=terminal_parts pub claims point lambda chi theta zc mu ∧
 reference pub claims point zc lambda chi theta mu=terminal_parts pub claims point lambda chi theta zc mu := by
 refine ⟨out,log,cuts,NLH_RustCuts.attempted_prefix cuts,canon,value,?_⟩
 unfold reference
 rw [NLH_RustCuts.result cuts]
 exact value
/-- Full263 parent fold, including complete237 Result and tuple channels.
The237 packet is applied internally at SAME arguments, never as a premise. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (hd : NKR_DigestChildren.Domain pub) (hc : canonical claims)
 (hp : canonical point) (hz : canonical zc) (hl : Canon lambda) (hchi : Canon chi)
 (ht : Canon theta) (hm : Canon mu) (asset : pub.asset_id.val < 2147483647) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial result events ∧
 events <+: order ∧ Canonical result ∧ projected result=terminal_parts pub claims point lambda chi theta zc mu ∧
 reference pub claims point zc lambda chi theta mu=terminal_parts pub claims point lambda chi theta zc mu := by
 obtain ⟨childResult,_,_,_,childCanonical,childEq,_⟩ := NLH_CompRoot.source pub claims point lambda chi theta hd hc hp hl hchi ht asset
 cases resultEq : childResult with
 | fail err =>
   have child : composition_parts pub claims point lambda chi theta=fail err := by rw [←childEq,resultEq];rfl
   have call : step pub claims point zc lambda chi theta mu .composition initial=fail err := by simp only [step,child,bind_tc_fail]
   have cuts : NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial (fail err) [.composition] := .failed call
   apply package pub claims point zc lambda chi theta mu _ _ cuts
   · rw [NLH_TermPartsFactor.source];unfold NLH_TermPartsFactor.reference;rw [child];rfl
   · trivial
 | div =>
   have child : composition_parts pub claims point lambda chi theta=div := by rw [←childEq,resultEq];rfl
   have call : step pub claims point zc lambda chi theta mu .composition initial=div := by simp only [step,child,bind_tc_div]
   have cuts : NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial div [.composition] := .diverged call
   apply package pub claims point zc lambda chi theta mu _ _ cuts
   · rw [NLH_TermPartsFactor.source];unfold NLH_TermPartsFactor.reference;rw [child];rfl
   · trivial
 | ok r =>
   cases r with
   | Err err =>
     have child : composition_parts pub claims point lambda chi theta=ok (.Err err) := by rw [←childEq,resultEq];rfl
     have call : step pub claims point zc lambda chi theta mu .composition initial=ok (.Err err) := by simp only [step,child,bind_tc_ok]
     have cuts : NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial (ok (.Err err)) [.composition] := .returned call
     apply package pub claims point zc lambda chi theta mu _ _ cuts
     · rw [NLH_TermPartsFactor.source];unfold NLH_TermPartsFactor.reference;rw [child];rfl
     · trivial
   | Ok childState =>
     let child := NLH_CompositionState.returned childState
     have called : composition_parts pub claims point lambda chi theta=ok (.Ok child) := by rw [←childEq,resultEq];rfl
     have canonicalChild : NLH_CompRoot.Canonical (ok (.Ok childState)) := by rw [←resultEq];exact childCanonical
     rcases canonicalChild with ⟨cc,cz,cm,cg,ch,ca⟩
     obtain ⟨calls,arithmetic,co,_⟩ := NKR_TermTail.result zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2 hz hp hm cc ch ca
     have start : NLH_PartsValues.stage child calls 0={initial with child := child} := by
       have zero : NLH_PartsValues.snapshot calls 0=(fun _ => field.QM31.ZERO) := by
         funext j;simp only [NLH_PartsValues.snapshot,Nat.not_lt_zero,ite_false]
       unfold NLH_PartsValues.stage
       rw [zero]
       rfl
     have call : step pub claims point zc lambda chi theta mu .composition initial=ok (.Ok (NLH_PartsValues.stage child calls 0)) := by
       rw [start];simp only [step,called,bind_tc_ok]
     have tail := NLH_PartsFold.arithmetic pub claims point zc lambda chi theta mu child calls
     let final := NLH_PartsValues.stage child calls 9
     have cuts : NLH_RustCuts.Cuts (step pub claims point zc lambda chi theta mu) order initial (ok (.Ok final)) order := .next call tail
     apply package pub claims point zc lambda chi theta mu _ _ cuts
     · rw [NLH_TermPartsFactor.source]
       unfold NLH_TermPartsFactor.reference
       rw [called,bind_tc_ok]
       simp only [NKR_TermTail.after,NKR_TermTail.tail,arithmetic,bind_tc_ok]
       rfl
     · exact ⟨co,cz,cm,cg⟩
#print axioms package
#print source
#print axioms source
end AspisR1.NLH_PartsRoot
end
