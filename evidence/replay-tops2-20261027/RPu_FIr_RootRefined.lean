import RPu_FIr_H1Canonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_RootRefined
open Aeneas Aeneas.Std Result
open FIr_TerminalTrace
open FIr_NativeValue (Canon decode K)

theorem parts (pub : SemPub) (claims : Array NQ 84#usize)
    (point zc : Array NQ 10#usize) (lambda chi theta mu out : NQ)
    (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize) (g : NQ)
    (success : FIr_TerminalTrace.parts pub claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g)))
    (hclaims : ∀ x∈claims.val,Canon x)
    (hl : ∀ x∈zc.val,Canon x) (hr : ∀ x∈point.val,Canon x) (hmu : Canon mu) :
    ∃ comp h active,
      composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)) ∧
      Canon h ∧ (Canon comp → Canon active →
        Canon out ∧ decode out=FIr_TerminalValue.formula
          (R0P.SemSource.eqValue (fun j : Fin 10=>FIr_NativeArray.value zc j.val)
            (fun j : Fin 10=>FIr_NativeArray.value point j.val))
          (decode comp) (decode mu) (decode h) (decode active)) := by
  obtain ⟨comp,h,active,called,value⟩ := FIr_TerminalPartsValue.reached_value
    pub claims point zc lambda chi theta mu out c1 mask g success hl hr hmu
  have hh := FIr_H1Canonical.canonical pub claims point lambda chi theta comp g h active c1 mask called hclaims
  exact ⟨comp,h,active,called,hh,fun hc ha=>value hc hh ha⟩

#print axioms parts
end AspisR1.FIr_RootRefined
end
