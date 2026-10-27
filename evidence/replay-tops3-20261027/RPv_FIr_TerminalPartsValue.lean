import RPv_FIr_TerminalValue
import RPv_FIr_EqualityProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_TerminalPartsValue
open Aeneas Aeneas.Std Result
open FIr_TerminalTrace
open FIr_NativeValue (Canon decode K)

theorem reached_value (pub : SemPub) (claims : Array NQ 84#usize)
    (point zc : Array NQ 10#usize) (lambda chi theta mu out : NQ)
    (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize) (g : NQ)
    (success : parts pub claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g)))
    (hl : ∀ x∈zc.val,Canon x) (hr : ∀ x∈point.val,Canon x) (hmu : Canon mu) :
    ∃ comp h active,
      composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)) ∧
      (Canon comp → Canon h → Canon active →
        Canon out ∧ decode out=FIr_TerminalValue.formula
          (R0P.SemSource.eqValue (fun j : Fin 10=>FIr_NativeArray.value zc j.val)
            (fun j : Fin 10=>FIr_NativeArray.value point j.val))
          (decode comp) (decode mu) (decode h) (decode active)) := by
  obtain ⟨comp,h,active,called,⟨calls⟩⟩ := reached pub claims point zc lambda chi theta mu out c1 mask g success
  refine ⟨comp,h,active,called,?_⟩
  intro hc hh ha
  have result := FIr_TerminalValue.arithmetic zc point mu comp h active out calls hl hr hmu hc hh ha
  rw [FIr_EqualityProduct.model] at result
  exact result

#print axioms reached_value
end AspisR1.FIr_TerminalPartsValue
end
