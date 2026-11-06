import NJX_PatternRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternForward
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- NJL_K055/056 exact deployed windowed-arm forwarding: one call with
same readonly opened16 and same lambda; complete14reply returned unchanged. -/
def Cut (o seen : Array NQ 16#usize) (lambda seenLambda : NQ)
 (child out : Array NQ 14#usize) (calls : Nat) : Prop :=
 calls=1 ∧ seen=o ∧ seenLambda=lambda ∧ out=child

/-- Complete223 positive root;224 is instantiated on SAME args and all of its
power/window/tail clauses stay in the conclusion. No child-success premise. -/
theorem source (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda)
 (ho : FIw_ArrayValue.canonical o) :
 ∃ (p : NJL_CachedPowers.Packet lambda) (w : Fin 4 → NQ) (out : Array NQ 14#usize),
 NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda=ok (NJL_CacheReads.power p,p.next) ∧
 NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda (NJL_CacheReads.power p) p.next ∧
 (∀ j,NJL_WindowFold.run (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO=ok (w j) ∧
 NJL_WindowFold.Trace (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8) FIq_Native.field.QM31.ZERO (w j)) ∧
 NJX_PatternTail.run p (NJX_PatternPacket.atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO)=ok (NJX_PatternRoot.cells out) ∧
 NJX_PatternTail.Trace p (NJX_PatternPacket.atoms o w) (List.finRange 14) (fun _=>FIq_Native.field.QM31.ZERO) (NJX_PatternRoot.cells out) ∧
 FIw_ArrayValue.canonical out ∧
 FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values o lambda=ok out ∧ Cut o o lambda lambda out out 1 := by
 obtain ⟨p,w,out,hp,ht,hw,tail,trace,hout,body⟩ := NJX_PatternRoot.source lambda o hl ho
 exact ⟨p,w,out,hp,ht,hw,tail,trace,hout,body,rfl,rfl,rfl,rfl⟩
#print source
#print axioms source
end AspisR1.NJX_PatternForward
end
