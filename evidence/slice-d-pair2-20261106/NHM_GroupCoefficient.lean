import NHI_RangeProgress

import NHM_ArrayPreserve
import NHM_ResultInvariant
import NHI_GroupTables
import NHE_FieldCanonical
set_option autoImplicit false
namespace NHM_GroupCoefficient
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells := Array NE 12#usize
abbrev Iter := NHI_RangeProgress.Range
abbrev State := Iter × Cells

def window (f : Slice U8) (j : Usize) (cells : Cells) : Result Cells := do
 let g ← Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j
 let group := UScalar.cast .Usize g
 let before ← Array.index_usize cells group
 let x ← FIo_Native.weights.field f j
 let after ← FIo_Native.aspis_core.field.wide_exact.WideExact.add before x
 Array.update cells group after

def body (f : Slice U8) (s : State) : Result (ControlFlow State Cells) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some j=>do let cells ← window f j s.2;ok (.cont (next,cells))

theorem step (f : Slice U8) (s : State) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2=body f s := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body body window
 simp only [lift,bind_assoc_eq,bind_tc_ok]
 rfl

theorem canonical (f : Slice U8) (j : Usize) (cells out : Cells)
 (small : j.val<64) (before : ∀ x∈cells.val,canonE x)
 (run : window f j cells=ok out) : ∀ x∈out.val,canonE x := by
 unfold window at run
 obtain ⟨g,hg,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨sum,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 have ca:=NHM_ArrayCanon.read canonE cells _ a before ha
 have cx:=NHE_FieldCanonical.success f j small x hx
 obtain ⟨sum',hs',cs⟩ := NGW_PolynomialAdd.total a x ca cx
 have equal : sum'=sum := Result.ok.inj (hs'.symm.trans hs)
 subst sum'
 exact NHM_ArrayPreserve.canonical canonE cells out _ sum before cs run

theorem progress (f : Slice U8) (s t : State) (run : body f s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact (NHI_RangeProgress.some_next s.1 next j hn).2

theorem decreases (f : Slice U8) (s t : State) (run : body f s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,more⟩ := progress f s t run
 have hv:=congrArg (fun x : Usize=>x.val) last
 omega

theorem source (f : Slice U8) (cells : Cells) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop0
  {start:=0#usize,«end»:=64#usize} f cells=
 NHI_CountedLoop.unroll (body f) 65 ({start:=0#usize,«end»:=64#usize},cells) := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0
 have same : (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2)=body f := funext (step f)
 rw [same]
 exact NHI_CountedLoop.agrees (body f) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f) 65 _ (by change (64:Nat)-0<65;omega)

#print axioms step
#print axioms canonical
#print axioms progress
#print axioms decreases
#print axioms source
end NHM_GroupCoefficient
