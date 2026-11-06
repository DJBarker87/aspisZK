import NLH_WrapperGathers
import NLH_PartsRoot
import NLH_TermWrapperFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_WrapperRoot
open Aeneas Aeneas.Std Result FIq_Native NLH_WrapperState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal
abbrev Outcome := Result (core.result.Result State NLH_WrapperState.Error)
def initial (pub : r0.Public) : State :=
 ⟨NLH_CompRun.zeros 84#usize,NKR_TermPublic.value pub,
  (field.QM31.ZERO,NLH_CompRun.zeros 16#usize,NLH_CompRun.zeros 10#usize,field.QM31.ZERO)⟩
def project : core.result.Result State NLH_WrapperState.Error → core.result.Result NQ NLH_WrapperState.Error
 | .Err e => .Err e
 | .Ok st => .Ok (returned st)
def projected (r : Outcome) := do let out ← r;ok (project out)
def Canonical : Outcome → Prop
 | .ok (.Ok st) => Canon (returned st)
 | _ => True
def reference (pub : r0.Public) (claims : Claims) (point : Array NQ 10#usize) (c : Challenges) := do
 let r ← NLH_FoldRust.run (step pub claims point c) order (initial pub)
 ok (project r)
theorem package (pub : r0.Public) (claims : Claims) (point : Array NQ 10#usize) (c : Challenges)
 (out : Outcome) (log : List Event)
 (cuts : NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) out log)
 (value : projected out=r0.Public.terminal_qm31 pub claims point c) (canon : Canonical out) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) result events ∧
 events <+: order ∧ Canonical result ∧ projected result=r0.Public.terminal_qm31 pub claims point c ∧
 reference pub claims point c=r0.Public.terminal_qm31 pub claims point c := by
 refine ⟨out,log,cuts,NLH_RustCuts.attempted_prefix cuts,canon,value,?_⟩
 unfold reference
 rw [NLH_RustCuts.result cuts]
 exact value
/-- Full256 source-order fold. Canonical full84 gather, SAME255 public,
SAME263 full Result, and both map/map_err arms are instantiated internally. -/
theorem source (pub : r0.Public) (claims : Claims) (point : Array NQ 10#usize) (c : Challenges)
 (hd : NKR_DigestChildren.Domain (NKR_TermPublic.value pub)) (hc : ∀ row∈claims.val,canonical row)
 (hp : canonical point) (hz : canonical c.zc) (hl : Canon c.lambda) (hchi : Canon c.chi)
 (ht : Canon c.theta) (hm : Canon c.mu) (asset : (NKR_TermPublic.value pub).asset_id.val < 2147483647) :
 ∃ result events,NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) result events ∧
 events <+: order ∧ Canonical result ∧ projected result=r0.Public.terminal_qm31 pub claims point c ∧
 reference pub claims point c=r0.Public.terminal_qm31 pub claims point c := by
 obtain ⟨selected,gathers,cs,sameSelected,gatherCall⟩ := NLH_WrapperGathers.source pub claims point c (initial pub) hc
 have start : NLH_WrapperGathers.stage claims (initial pub) 0=initial pub := by
   unfold NLH_WrapperGathers.stage
   have cells : (fun j => if j.val < 0 then selectedCell claims j else NJB_ArrayCarrier.cell (initial pub).selected j)=
       NJB_ArrayCarrier.cell (initial pub).selected := by funext j;simp only [Nat.not_lt_zero,ite_false]
   rw [cells,NJB_ArrayCarrier.array_cell]
 rw [start] at gathers
 let beforePublic := NLH_WrapperGathers.stage claims (initial pub) 84
 let afterPublic : State := {beforePublic with semanticPublic := NKR_TermPublic.value pub}
 have publicCall := NLH_WrapperState.semantic_step pub claims point c beforePublic
 obtain ⟨selected',gather',_,wrapper⟩ := NLH_TermWrapperFactor.source pub claims point c hc
 have unique : selected'=selected := Result.ok.inj (gather'.symm.trans gatherCall)
 rw [unique] at wrapper
 obtain ⟨partsResult,_,_,_,partsCanonical,partsEq,_⟩ := NLH_PartsRoot.source (NKR_TermPublic.value pub) selected point c.zc
   c.lambda c.chi c.theta c.mu hd cs hp hz hl hchi ht hm asset
 cases resultEq : partsResult with
 | fail err =>
   have child : terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu=fail err := by rw [←partsEq,resultEq];rfl
   have called : terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=fail err := by
     change terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=_
     rw [sameSelected];exact child
   have suffix : NLH_RustCuts.Cuts (step pub claims point c) [.semantic,.parts] beforePublic (fail err) [.semantic,.parts] :=
     .next publicCall (.failed (by simp only [step,afterPublic,called,bind_tc_fail]))
   have cuts : NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) (fail err) ((List.finRange 84).map Event.gather ++ [.semantic,.parts]) := NLH_FoldAppend.rust gathers suffix
   apply package pub claims point c _ _ cuts
   · rw [wrapper];unfold NLH_TermWrapperFactor.reference;rw [child];rfl
   · trivial
 | div =>
   have child : terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu=div := by rw [←partsEq,resultEq];rfl
   have called : terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=div := by
     change terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=_
     rw [sameSelected];exact child
   have suffix : NLH_RustCuts.Cuts (step pub claims point c) [.semantic,.parts] beforePublic div [.semantic,.parts] :=
     .next publicCall (.diverged (by simp only [step,afterPublic,called,bind_tc_div]))
   have cuts : NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) div ((List.finRange 84).map Event.gather ++ [.semantic,.parts]) := NLH_FoldAppend.rust gathers suffix
   apply package pub claims point c _ _ cuts
   · rw [wrapper];unfold NLH_TermWrapperFactor.reference;rw [child];rfl
   · trivial
 | ok r =>
   cases r with
   | Err err =>
     have child : terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu=ok (.Err err) := by rw [←partsEq,resultEq];rfl
     have called : terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=ok (.Err err) := by
       change terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=_
       rw [sameSelected];exact child
     have suffix : NLH_RustCuts.Cuts (step pub claims point c) [.semantic,.parts] beforePublic (ok (.Err .Public)) [.semantic,.parts] :=
       .next publicCall (.returned (by simp only [step,afterPublic,called,bind_tc_ok]))
     have cuts : NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) (ok (.Err .Public)) ((List.finRange 84).map Event.gather ++ [.semantic,.parts]) := NLH_FoldAppend.rust gathers suffix
     apply package pub claims point c _ _ cuts
     · rw [wrapper];unfold NLH_TermWrapperFactor.reference;rw [child];rfl
     · trivial
   | Ok partsState =>
     let parts := NLH_PartsState.returned partsState
     have child : terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu=ok (.Ok parts) := by rw [←partsEq,resultEq];rfl
     have called : terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=ok (.Ok parts) := by
       change terminal_parts (NKR_TermPublic.value pub) beforePublic.selected point c.lambda c.chi c.theta c.zc c.mu=_
       rw [sameSelected];exact child
     let final : State := {afterPublic with parts := parts}
     have suffix : NLH_RustCuts.Cuts (step pub claims point c) [.semantic,.parts] beforePublic (ok (.Ok final)) [.semantic,.parts] :=
       .next publicCall (.next (by simp only [step,afterPublic,called,bind_tc_ok]) (.nil final))
     have cuts : NLH_RustCuts.Cuts (step pub claims point c) order (initial pub) (ok (.Ok final)) ((List.finRange 84).map Event.gather ++ [.semantic,.parts]) := NLH_FoldAppend.rust gathers suffix
     apply package pub claims point c _ _ cuts
     · rw [wrapper];unfold NLH_TermWrapperFactor.reference;rw [child];rfl
     · have canon : NLH_PartsRoot.Canonical (ok (.Ok partsState)) := by rw [←resultEq];exact partsCanonical
       exact canon.1
#print axioms package
#print source
#print axioms source
end AspisR1.NLH_WrapperRoot
end
