import FIo_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FromLimbsUnwrap
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem canonical (limbs : Array U32 8#usize) (o : Option NE) (out : NE)
    (read : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs limbs=ok o)
    (unwrap : core.option.Option.unwrap o=ok out) : FIo_WideValues.Canon out := by
  cases o with
  | none => simp only [core.option.Option.unwrap] at unwrap; cases unwrap
  | some x =>
    have same : x=out := Result.ok.inj unwrap
    subst out
    exact FIo_FromLimbs.canonical limbs x read

#print axioms canonical
end AspisR1.FIp_FromLimbsUnwrap
end
