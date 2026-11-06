import NJX_PatternAssociation
import NJX_PatternMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
theorem size14 : (14#usize).val=14 := by scalar_tac

def cells (a : Array NQ 14#usize) (i : Fin 14) : NQ :=
 FIw_ArrayValue.cells a ⟨i.val,by rw [size14];exact i.isLt⟩

/-- Complete224 native-cut invocation and exact adopted cohort Result on SAME
lambda/openings. Constructor, powers, windows, all14tail arithmetic Results,
all frames and canonical output equality are derived internally. -/
theorem source (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda)
 (ho : FIw_ArrayValue.canonical o) :
 ∃ (p : NJL_CachedPowers.Packet lambda) (w : Fin 4 → NQ) (out : Array NQ 14#usize),
 NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda=ok (NJL_CacheReads.power p,p.next) ∧
 NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda (NJL_CacheReads.power p) p.next ∧
 (∀ j,NJL_WindowFold.run (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO=ok (w j) ∧
 NJL_WindowFold.Trace (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO (w j)) ∧
 NJX_PatternTail.run p (NJX_PatternPacket.atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO)=ok (cells out) ∧
 NJX_PatternTail.Trace p (NJX_PatternPacket.atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO) (cells out) ∧
 FIw_ArrayValue.canonical out ∧
 FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values o lambda=ok out := by
 obtain ⟨p,w,after,pc,pt,hw,tc,tt,ha,va⟩ := NJX_PatternPacket.source lambda o hl ho
 obtain ⟨out,body,hout,vout⟩ := NJX_PatternAssociation.cohort lambda o hl ho
 have av := NJX_PatternAssociation.atoms_value lambda o w (fun j=>(hw j).2.2.2)
 have same : after=cells out := by
  funext i
  apply NJB_DecodeInjective.qm _ _ (ha i) (hout _ (List.getElem_mem _))
  rw [va,av]
  change NJX_PatternModel.model (FIw_ArrayValue.decoded o) (decode lambda) i=FIw_ArrayValue.decoded out _
  rw [vout]
  exact NJX_PatternMeaning.value _ _ i
 rw [same] at tc tt
 exact ⟨p,w,out,pc,pt,(fun j=>⟨(hw j).1,(hw j).2.1⟩),tc,tt,hout,body⟩
#print source
#print axioms size14
#print axioms source
end AspisR1.NJX_PatternRoot
end
