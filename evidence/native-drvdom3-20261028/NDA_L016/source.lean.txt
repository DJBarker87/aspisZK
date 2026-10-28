import NDA_PowerDomain
import NBZ_Folds
import NCG_HornerLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDA_LaneDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

theorem wide_iff (x : Stage2E) :
    NBO_TailDomain.WideCanonical x ↔ Port4C_QueryArithmetic.CanonE x :=
  and_congr (NDA_PowerDomain.canonical_iff x.c0) (NDA_PowerDomain.canonical_iff x.c1)

/-- The existing query-lane primitive bindings imply three of the four
canonicality laws on precisely the ops they bind. The line law remains named.
This never replaces c.query with a new arithmetic dictionary. -/
theorem of_bindings (ops : Ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
    (line : ∀ alpha values inverse out, ops.op16 alpha values inverse = ok out →
      Port4C_QueryArithmetic.CanonE out) : NDA_QueryCanonical.Laws ops := by
  have facts := NBO_FieldSemantics.fields ops bindings
  refine ⟨?_,?_,?_,line⟩
  · intro x q out hx hq run
    exact (wide_iff out).mp (facts.product x q out ((wide_iff x).mpr hx)
      ((NDA_PowerDomain.canonical_iff q).mpr hq) run)
  · intro x y out hx hy run
    exact (wide_iff out).mp (facts.sum x y out ((wide_iff x).mpr hx)
      ((wide_iff y).mpr hy) run)
  · exact NDA_PowerDomain.of_binding ops bindings.power

/-- The line-lane arithmetic result supplies canonicality on its proved
canonical-input domain, when the actual op16 return is locally associated.
It does NOT prove the unconditional line law of an arbitrary ops record. -/
theorem line_result (ops : Ops) (alpha a b c d : Stage2E)
    (inverse : Array U32 5#usize) (quarter qiz hix hiy half hiz : U32) (out : Stage2E)
    (halpha : Port4C_QueryArithmetic.CanonE alpha)
    (ha : Port4C_QueryArithmetic.CanonE a) (hb : Port4C_QueryArithmetic.CanonE b)
    (hc : Port4C_QueryArithmetic.CanonE c) (hd : Port4C_QueryArithmetic.CanonE d)
    (binding : ops.op16 alpha (Array.make 4#usize [a,b,c,d]) inverse =
      NBZ_Folds.line alpha a b c d quarter qiz hix hiy half hiz)
    (call : ops.op16 alpha (Array.make 4#usize [a,b,c,d]) inverse = ok out) :
    Port4C_QueryArithmetic.CanonE out := by
  obtain ⟨value,run,canonical⟩ := NBZ_Folds.line_total alpha a b c d quarter qiz hix hiy half hiz
    ((wide_iff alpha).mpr halpha) ((wide_iff a).mpr ha) ((wide_iff b).mpr hb)
    ((wide_iff c).mpr hc) ((wide_iff d).mpr hd)
  have same := Result.ok.inj (run.symm.trans (binding.symm.trans call))
  exact (wide_iff out).mp (same ▸ canonical)

#print axioms wide_iff
#print axioms of_bindings
#print axioms line_result
end AspisR1.NDA_LaneDomains
end
