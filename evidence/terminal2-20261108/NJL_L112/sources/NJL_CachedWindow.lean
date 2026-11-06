import NJL_WindowFold
import NJL_CacheReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_CachedWindow
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Complete8step native window invocation and value, using ONE internally
constructed powers/cache packet shared by every start (in particular0,1,2,8).
This is224 SUPPORT until mutable-power-array and14tail/cohort roots compose. -/
theorem source (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda) (ho : FIw_ArrayValue.canonical o) :
 ∃ p : NJL_CachedPowers.Packet lambda,∀ start : Fin 9,∃ after,
 NJL_WindowFold.run (NJL_CacheReads.cache p) o start (List.finRange 8) FIq_Native.field.QM31.ZERO=ok after ∧
 NJL_WindowFold.Trace (NJL_CacheReads.cache p) o start (List.finRange 8) FIq_Native.field.QM31.ZERO after ∧
 Canon after ∧ decode after=(List.ofFn (fun i : Fin 8=>decode lambda^(i.val+1)*decode (NJL_WindowStep.opened o start i))).sum := by
 obtain ⟨p⟩ := NJL_CachedPowers.source lambda hl
 refine ⟨p,?_⟩
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
end AspisR1.NJL_CachedWindow
end
