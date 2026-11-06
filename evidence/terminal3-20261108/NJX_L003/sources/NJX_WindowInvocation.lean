import NJL_WindowPowerArray
import NJL_CachedWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_WindowInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Complete224 PREFIX on one internally constructed source packet: all8
mutable saves/products (including unused final product), actual std8cache map,
and every complete8step window on SAME powers/cache/openings. This is SUPPORT:
the14tail/cohort association is still an OPEN full-function obligation. -/
theorem source (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda) (ho : FIw_ArrayValue.canonical o) :
 ∃ p : NJL_CachedPowers.Packet lambda,
 NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda=ok (NJL_CacheReads.power p,p.next) ∧
 NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda (NJL_CacheReads.power p) p.next ∧
 ∀ start : Fin 9,∃ after,
 NJL_WindowFold.run (NJL_CacheReads.cache p) o start (List.finRange 8) FIq_Native.field.QM31.ZERO=ok after ∧
 NJL_WindowFold.Trace (NJL_CacheReads.cache p) o start (List.finRange 8) FIq_Native.field.QM31.ZERO after ∧
 Canon after ∧ decode after=(List.ofFn (fun i : Fin 8=>decode lambda^(i.val+1)*decode (NJL_WindowStep.opened o start i))).sum := by
 obtain ⟨p,powerCall,powerTrace⟩ := NJL_WindowPowerArray.source lambda hl
 refine ⟨p,powerCall,powerTrace,?_⟩
 intro start
 obtain ⟨after,call,trace,ha,value⟩ := NJL_WindowFold.source (NJL_CacheReads.power p) (NJL_CacheReads.cache p) o start
  (List.finRange 8) FIq_Native.field.QM31.ZERO (NJL_CacheReads.canonical p) FIv_NativeValue.zero.1 ho
  (fun i=>(NJL_CacheReads.constructor p i).2)
 refine ⟨after,call,trace,ha,?_⟩
 rw [value,FIv_NativeValue.zero.2,zero_add]
 congr 1
 change List.ofFn (fun i : Fin 8=>decode (NJL_CacheReads.power p i)*decode (NJL_WindowStep.opened o start i))=_
 congr 1
 funext i
 rw [NJL_CacheReads.value]
#print source
#print axioms source
end AspisR1.NJX_WindowInvocation
end
