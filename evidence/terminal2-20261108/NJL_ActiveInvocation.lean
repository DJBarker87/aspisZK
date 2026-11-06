import NJL_LowDischarge
import NJB_CutDischarge
import NJB_ActiveAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_ActiveInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- SAME source-order high native window plus its complete actual child Result.
The modifies set is exactly the selected coordinate; all other cells are framed.
Native certificate: NJB_K014/K015, NJB_active.rs.txt high assertions. -/
def HighStep (source : Fin 64 → NQ) (before after : Fin 7 → NQ) (b : Fin 64) : Prop :=
 ∃ reply event, FIq_Native.field.QM31.add (before (NJB_ActiveModel.key b)) (source b)=ok reply ∧
 NJB_Cuts.high source before after b reply event 1 (b.val+1)
/-- SAME source-order low window, every entered call discharged at its exact
arguments; unused canonical replies are ZERO. K020/021..K032/033. -/
def LowStep (high : Fin 7 → NQ) (low : Fin 16 → NQ) (before after : NQ) (c : Fin 7) : Prop :=
 ∃ r events, NJL_LowDischarge.Clauses high low before r c ∧
 NJB_Cuts.low high low before r c events (NJB_Cuts.lowCount c+1) (c.val+1) after
inductive HighTrace (source : Fin 64 → NQ) : List (Fin 64) → (Fin 7 → NQ) → (Fin 7 → NQ) → Prop
 | nil (s) : HighTrace source [] s s
 | cons {b bs s next last} : HighStep source s next b → HighTrace source bs next last →
   HighTrace source (b::bs) s last
inductive LowTrace (high : Fin 7 → NQ) (low : Fin 16 → NQ) : List (Fin 7) → NQ → NQ → Prop
 | nil (s) : LowTrace high low [] s s
 | cons {c cs s next last} : LowStep high low s next c → LowTrace high low cs next last →
   LowTrace high low (c::cs) s last
/-- Positive cut with the actual emitted add, not an independent output seed. -/
theorem high_step (source : Fin 64 → NQ) (before : Fin 7 → NQ) (b : Fin 64)
 (hh : ∀ i,Canon (source i)) (hs : ∀ i,Canon (before i)) :
 ∃ after, HighStep source before after b ∧ (∀ i,Canon (after i)) ∧
 NJB_ActiveRawHigh.step source before b=ok after := by
 obtain ⟨reply,call,hr,_⟩ := NJB_StubLaws.qm_add (before (NJB_ActiveModel.key b)) (source b) (hs _) (hh _)
 let after := fun i=>if NJB_ActiveModel.key b=i then reply else before i
 have key : R0P.activeMaskCoordinate (NJB_MaskTable.nativeMasks b)=NJB_ActiveModel.key b := by
  rw [NJB_MaskTable.source_eq_model];rfl
 refine ⟨after,⟨reply,⟨1,before (NJB_ActiveModel.key b),source b⟩,call,?_⟩,?_,?_⟩
 · unfold NJB_Cuts.high
   rw [key]
   exact ⟨hs _,hh _,hr,rfl,rfl,rfl,rfl,rfl,fun _=>rfl⟩
 · intro i
   dsimp [after]
   split <;> first | exact hr | exact hs i
 · simp only [NJB_ActiveRawHigh.step,call,bind_tc_ok]
   rfl
/-- Complete low cut, with its final native reply consumed by the source step. -/
theorem low_step (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (c : Fin 7)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon sum) :
 ∃ after, LowStep high low sum after c ∧ Canon after ∧
 NJB_ActiveRawLow.step high low sum c=ok after := by
 obtain ⟨r,hr,clauses,discharge⟩ := NJL_LowDischarge.source high low sum c hh hl hs
 let out := r ⟨NJB_Cuts.lowCount c,by have := NJB_Cuts.low_count_bound c;omega⟩
 let events := fun j : Fin (NJB_Cuts.lowCount c+1)=>
  (⟨if j.val=NJB_Cuts.lowCount c-1 then 0 else 1,
    NJB_Cuts.lowLeft high low sum r c j,NJB_Cuts.lowRight low r c j⟩ : NJB_Cuts.Event)
 have cut : NJB_Cuts.low high low sum r c events (NJB_Cuts.lowCount c+1) (c.val+1) out :=
  ⟨hh,hl,hs,hr,rfl,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩⟩
 exact ⟨out,⟨r,events,clauses,cut⟩,hr _,discharge events _ _ out cut⟩
theorem high_run (source : Fin 64 → NQ) (bs : List (Fin 64)) (before : Fin 7 → NQ)
 (hh : ∀ i,Canon (source i)) (hs : ∀ i,Canon (before i)) :
 ∃ after,HighTrace source bs before after ∧ (∀ i,Canon (after i)) ∧
 NJB_ActiveRawHigh.run source bs before=ok after := by
 induction bs generalizing before with
 | nil => exact ⟨before,.nil _,hs,rfl⟩
 | cons b bs ih =>
  obtain ⟨next,cut,hn,call⟩ := high_step source before b hh hs
  obtain ⟨last,trace,hl,rest⟩ := ih next hn
  exact ⟨last,.cons cut trace,hl,by simp only [NJB_ActiveRawHigh.run,call,bind_tc_ok,rest]⟩
theorem low_run (high : Fin 7 → NQ) (low : Fin 16 → NQ) (cs : List (Fin 7)) (before : NQ)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon before) :
 ∃ after,LowTrace high low cs before after ∧ Canon after ∧
 NJB_ActiveRawLow.run high low cs before=ok after := by
 induction cs generalizing before with
 | nil => exact ⟨before,.nil _,hs,rfl⟩
 | cons c cs ih =>
  obtain ⟨next,cut,hn,call⟩ := low_step high low before c hh hl hs
  obtain ⟨last,trace,hLast,rest⟩ := ih next hn
  exact ⟨last,.cons cut trace,hLast,by simp only [NJB_ActiveRawLow.run,call,bind_tc_ok,rest]⟩
/-- Complete positive root: both finite native-cut traces, all frames and child
clauses, followed by the adopted cohort's full Result on the SAME selectors.
Only canonical input domains occur in the statement. Physical native transport
is the reviewed (y)/(ai)(5)/(aq)(5) reclassification; no inverse-log premise. -/
theorem source (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ grouped out,
 HighTrace (NJB_ActiveReference.high s) (List.ofFn (fun b : Fin 64=>b))
  (fun _=>FIq_Native.field.QM31.ZERO) grouped ∧
 LowTrace grouped (NJB_ActiveReference.low s) (List.ofFn (fun c : Fin 7=>c))
  FIq_Native.field.QM31.ZERO out ∧ Canon out ∧
 NJB_ActiveReference.reference s=ok out ∧
 FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.active s=ok out := by
 have hhigh (b : Fin 64) : Canon (NJB_ActiveReference.high s b) := hh _ (List.getElem_mem _)
 have hlow (c : Fin 16) : Canon (NJB_ActiveReference.low s c) := hl _ (List.getElem_mem _)
 obtain ⟨grouped,highTrace,hg,hcall⟩ := high_run (NJB_ActiveReference.high s)
  (List.ofFn (fun b : Fin 64=>b)) (fun _=>FIq_Native.field.QM31.ZERO) hhigh (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨out,lowTrace,ho,lcall⟩ := low_run grouped (NJB_ActiveReference.low s)
  (List.ofFn (fun c : Fin 7=>c)) FIq_Native.field.QM31.ZERO hg hlow FIv_NativeValue.zero.1
 have reference : NJB_ActiveReference.reference s=ok out := by
  simp only [NJB_ActiveReference.reference,hcall,lcall,bind_tc_ok]
 exact ⟨grouped,out,highTrace,lowTrace,ho,reference,(NJB_ActiveAssociation.result s hh hl).symm.trans reference⟩
#print source
#print axioms high_step
#print axioms low_step
#print axioms high_run
#print axioms low_run
#print axioms source
end AspisR1.NJL_ActiveInvocation
end
