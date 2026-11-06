import NJL_WindowPowerOverwrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowPowerArray
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- Complete mutable power-array invocation, internally SAME actual powers8
and cache-map packet; every untouched-cell frame and unused ninth power are
retained. Only14tail/cohort assembly remains for the entire224 function. -/
theorem source (lambda : NQ) (hl : Canon lambda) :
 ∃ p : NJL_CachedPowers.Packet lambda,
 NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda=ok (NJL_CacheReads.power p,p.next) ∧
 NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun _=>FIq_Native.field.QM31.ZERO) lambda (NJL_CacheReads.power p) p.next := by
 obtain ⟨p⟩ := NJL_CachedPowers.source lambda hl
 obtain ⟨after,call,trace,frame⟩ := NJL_WindowPowerFrame.lift lambda p.power_trace (List.finRange 8) (by simp) (fun _=>FIq_Native.field.QM31.ZERO) hl hl
 have same : after=NJL_CacheReads.power p := by
  rw [frame,←NJL_WindowPowerOverwrite.power_list p]
  exact NJL_WindowPowerOverwrite.overwrite _ _
 rw [same] at call trace
 exact ⟨p,call,trace⟩
#print source
#print axioms source
end AspisR1.NJL_WindowPowerArray
end
