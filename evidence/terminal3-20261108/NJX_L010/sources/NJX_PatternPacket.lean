import NJX_PatternTail
import NJB_ArrayCarrier
import FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
def starts : Fin 4 → Fin 9 := ![0,1,2,8]
def constant : NQ := FIw_ScalarArithmetic.lifted 1051521018#u32
theorem constant_canonical : Canon constant := (FIw_ScalarArithmetic.lift_value _ (by decide)).1
theorem constant_value : decode constant=(1051521018 : K) := by
 exact (FIw_ScalarArithmetic.lift_value _ (by decide)).2

def atoms (o : Array NQ 16#usize) (w : Fin 4 → NQ) (i : Fin 21) : NQ :=
 if h : i.val<16 then NJB_ArrayCarrier.cell o ⟨i.val,by scalar_tac⟩
 else if h2 : i.val<20 then w ⟨i.val-16,by omega⟩ else constant

theorem atoms_canonical (o : Array NQ 16#usize) (w : Fin 4 → NQ)
 (ho : FIw_ArrayValue.canonical o) (hw : ∀ i,Canon (w i)) : ∀ i,Canon (atoms o w i) := by
 intro i
 unfold atoms
 split
 · exact NJB_ArrayCarrier.canonical_cell o ho _
 · split
   · exact hw _
   · exact constant_canonical

/-- SAME power packet, SAME opened16, four captured window replies, all14
actual tail arithmetic Results, and the complete ZERO-initialized frame chain.
No free reply or successful-child clause is an input. SUPPORT until cohort join. -/
theorem source (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda)
 (ho : FIw_ArrayValue.canonical o) :
 ∃ (p : NJL_CachedPowers.Packet lambda) (w : Fin 4 → NQ) (out : NJX_PatternTail.State),
 NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda=ok (NJL_CacheReads.power p,p.next) ∧
 NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda (NJL_CacheReads.power p) p.next ∧
 (∀ j,NJL_WindowFold.run (NJL_CacheReads.cache p) o (starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO=ok (w j) ∧
 NJL_WindowFold.Trace (NJL_CacheReads.cache p) o (starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO (w j) ∧
 Canon (w j) ∧ decode (w j)=(List.ofFn (fun i : Fin 8=>decode lambda^(i.val+1)*decode (NJL_WindowStep.opened o (starts j) i))).sum) ∧
 NJX_PatternTail.run p (atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO)=ok out ∧
 NJX_PatternTail.Trace p (atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO) out ∧
 (∀ i,Canon (out i)) ∧
 ∀ i,decode (out i)=NJX_TailExpr.value (decode lambda) (fun k=>decode (atoms o w k)) (NJX_PatternTail.expr i) := by
 obtain ⟨p,pc,pt,windows⟩ := NJX_WindowInvocation.source lambda o hl ho
 choose w wc wt wh wv using (fun j : Fin 4=>windows (starts j))
 obtain ⟨out,co,tr,hout,vout⟩ := NJX_PatternTail.source p (atoms o w) (atoms_canonical o w ho wh)
  (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO) (fun _=>FIv_NativeValue.zero.1)
 refine ⟨p,w,out,pc,pt,(fun j=>⟨wc j,wt j,wh j,wv j⟩),co,tr,hout,?_⟩
 intro i
 simpa using vout i
#print source
#print axioms constant_canonical
#print axioms constant_value
#print axioms atoms_canonical
#print axioms source
end AspisR1.NJX_PatternPacket
end
