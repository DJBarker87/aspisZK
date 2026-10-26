import FIr_GatherCallback
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_GatherCanonical
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic (NQ)
open FIr_NativeValue (Canon)
open FIr_GatherCallback
abbrev callback := FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

theorem gathered (claims : Claims) (out : Array NQ 84#usize) (all : CanonClaims claims)
    (run : FIq_Native.array_from_fn_copy 84#usize FIq_Native.field.QM31.Insts.CoreMarkerCopy
      callback FIq_Native.field.QM31.ZERO claims=ok out) : ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 84#usize callback CanonClaims Canon _ claims out all run
  intro c i x c' initial called
  have one := selected c i x c' initial called
  exact ⟨one.1,one.2 ▸ initial⟩

#print axioms gathered
end AspisR1.FIr_GatherCanonical
end
