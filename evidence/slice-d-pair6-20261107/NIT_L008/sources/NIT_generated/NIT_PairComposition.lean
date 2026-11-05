import NIT_FieldInterpretation
import NIT_ArrayFrames
import NIG_CommonPost
import NIG_LowPost
import NHX_FinalTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PairComposition
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation

/-- Complete finite-array identity from Common's selected-cell and frame assertions. -/
theorem common_frame (row2 row3 : Array K 4#usize) (j : Nat)
 (before after : CommonCells) (l : Common) (cut : cutCommon row2 row3 j before l after) :
 after=NIT_ArrayFrames.put before j l.reply :=
 NIT_ArrayFrames.update FIo_Native.aspis_core.field.QM31.ZERO before after j l.reply cut.1 cut.2.2.2.2

/-- The analogous exact Low update, without interpreting its arithmetic reply. -/
theorem low_frame (ap0 ap1 : Powers) (s : Nat) (before after : LowCells)
 (l : Low) (cut : cutLow ap0 ap1 s before l after) :
 after=NIT_ArrayFrames.put before s l.scaled := by
 rcases cut with ⟨hs,_,_,_,_,_,_,_,_,_,_,_,_,_,frame⟩
 exact NIT_ArrayFrames.update NHI_Scalar.zero before after s l.scaled hs frame

theorem libra_frame (f : Ref (Slice U8)) (libra : Powers) (j : Nat)
 (before after : Parts) (l : LibraLog) (cut : cutLibraLog f libra j before l after) :
 after=NIT_ArrayFrames.put before 4 l.reply := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,frame⟩
 exact NIT_ArrayFrames.update NHI_Scalar.zero before after 4 l.reply (by decide) frame

theorem epick_index {n : Usize} (xs : Array E n) (i : Usize) (hi : i.val<n.val) :
 Array.index_usize xs i=ok (epick xs i.val) := by
 rw [NHI_ScalarDomain.index xs i hi]
 have bound : i.val<xs.val.length := by rw [xs.property];exact hi
 simp only [epick,List.getElem?_eq_getElem bound,Option.getD_some,NHI_ScalarDomain.pick]

theorem epick_canonical {n : Usize} (xs : Array E n) (hc : canonical xs) (i : Nat) :
 canonE (epick xs i) := by
 unfold epick
 cases h : xs.val[i]? with
 | none => exact NHI_Scalar.zero_canonical
 | some x => exact hc x (List.mem_of_getElem? h)

/-- Closed arithmetic packets are applied to the very operands logged by Final.
The two natural-number laws are individual field-stub specifications, not a
pair result or a successful enclosing execution assumption. -/
theorem final_cell (parts powers : Parts) (kind : Nat) (before after : E) (l : Final)
 (cut : cutFinal parts powers kind before l after)
 (mulLaw : EMul l.mul_a l.mul_b l.product)
 (addLaw : EAdd l.add_a l.add_b l.reply) :
 NHX_FinalFold.cell before (epick powers kind) (epick parts kind)=ok after ∧ canonE after := by
 rcases cut with ⟨_,cp,ck,cb,_,_,ma,mb,aa,ab,_,_,out⟩
 have cm := em l.mul_a l.mul_b l.product
  (ma.symm ▸ epick_canonical powers ck kind) (mb.symm ▸ epick_canonical parts cp kind) mulLaw
 have ca := ea l.add_a l.add_b l.reply (aa.symm ▸ cb) (ab.symm ▸ cm.2) addLaw
 rw [ma,mb] at cm
 rw [aa,ab] at ca
 refine ⟨?_,out.symm ▸ ca.2⟩
 simp only [NHX_FinalFold.cell,cm.1,bind_tc_ok,ca.1,out]

/-- One native iteration on arbitrary pre-state, associated to the exact emitted
FinalLoop body. The iterator bridge is the existing CLOSED range law. -/
theorem final_step (parts powers : Parts) (s : NHX_FinalLoop.State) (l : Final) (after : E)
 (cut : cutFinal parts powers s.1.start.val s.2 l after)
 (mulLaw : EMul l.mul_a l.mul_b l.product) (addLaw : EAdd l.add_a l.add_b l.reply)
 (last : s.1.end.val=7) :
 ∃ rest, NHX_FinalLoop.body parts powers s=ok (.cont (rest,after)) ∧
 rest.end.val=7 ∧ rest.start.val=s.1.start.val+1 ∧ canonE after := by
 have small := cut.1
 obtain ⟨rest,hn,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
 have cell := final_cell parts powers s.1.start.val s.2 after l cut mulLaw addLaw
 refine ⟨rest,?_,by rw [he];exact last,inc,cell.2⟩
 simp only [NHX_FinalLoop.body,hn,bind_tc_ok,epick_index parts s.1.start small,
  epick_index powers s.1.start small,cell.1]

/-- A chronological native trace consists only of cut-local observations and
individual callee specifications. No endpoint equation is an element. -/
inductive FinalTrace (parts powers : Parts) : Nat → NHX_FinalLoop.State → E → Prop
 | done (fuel : Nat) (s : NHX_FinalLoop.State) (stop : s.1.end.val ≤ s.1.start.val) :
   FinalTrace parts powers (fuel+1) s s.2
 | step (fuel : Nat) (s : NHX_FinalLoop.State) (out after : E) (l : Final)
   (cut : cutFinal parts powers s.1.start.val s.2 l after)
   (mulLaw : EMul l.mul_a l.mul_b l.product)
   (addLaw : EAdd l.add_a l.add_b l.reply)
   (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : FinalTrace parts powers fuel (rest,after) out) :
   FinalTrace parts powers (fuel+1) s out

/-- Rule B: finite induction of the SAME sum, parts and powers through all cuts. -/
theorem final_induction (parts powers : Parts) (fuel : Nat)
 (s : NHX_FinalLoop.State) (out : E) (trace : FinalTrace parts powers fuel s out) :
 NHI_CountedLoop.unroll (NHX_FinalLoop.body parts powers) fuel s=ok out := by
 induction trace with
 | done fuel s stop =>
   have next := NHI_ForwardRange.done s.1 stop
   simp only [NHI_CountedLoop.unroll,NHX_FinalLoop.body,next,bind_tc_ok]
 | step fuel s out after l cut mulLaw addLaw rest next tail ih =>
   have cell := (final_cell parts powers s.1.start.val s.2 after l cut mulLaw addLaw).1
   have body : NHX_FinalLoop.body parts powers s=ok (.cont (rest,after)) := by
    simp only [NHX_FinalLoop.body,next,bind_tc_ok,epick_index parts s.1.start cut.1,
     epick_index powers s.1.start cut.1,cell]
   simp only [NHI_CountedLoop.unroll,body,bind_tc_ok,ih]

/-- Complete seven-part fold association, including the last returned scalar.
This closes the final-loop subchain only; parent pair/finish remain OPEN. -/
theorem final_loop (parts powers : Parts) (out : E)
 (trace : FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) out) :
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize}
  parts powers NHI_Scalar.zero=ok out := by
 rw [NHX_FinalLoop.source]
 exact final_induction parts powers 8 _ out trace

#print axioms common_frame
#print axioms low_frame
#print axioms libra_frame
#print axioms epick_index
#print axioms epick_canonical
#print axioms final_cell
#print axioms final_step
#print axioms final_induction
#print axioms final_loop
end AspisR1.NIT_PairComposition
