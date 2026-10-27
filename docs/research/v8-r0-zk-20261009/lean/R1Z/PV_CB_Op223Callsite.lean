import R1Z.PV_CB_Op223TupleSupport
import R1Z.PV_CB_Op223Domain
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223Callsite
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op223CellSupport
variable [ExternalTypes]
abbrev Trace := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
abbrev Tuple := aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1
abbrev Values := alloc.vec.Vec (Array (Array Q 2#usize) 2#usize)
abbrev Arity := alloc.vec.Vec (Array Usize 2#usize)

theorem array_agree (ops : ExternalFuns) (f g : Compressor)
    (agree : ∀ tag values lambda, PV_CB_Op223Domain.Canonical values →
      f tag values lambda = g tag values lambda)
    (tag : M) (values : Array M 16#usize) (lambda : Q) :
    f tag (Array.to_slice values) lambda = g tag (Array.to_slice values) lambda :=
  agree tag _ lambda (@PV_CB_Op223Domain.array_domain _ ops values)

/-- Actual extracted caller transport: agreement is needed only on length16
    slices. All callback failures, inner errors, bounds failures and divergence
    remain in this equation. Numerical canonicality is a separate obligation. -/
theorem endpoint (ops : ExternalFuns) (f g : Compressor)
    (agree : ∀ tag values lambda, PV_CB_Op223Domain.Canonical values →
      f tag values lambda = g tag values lambda)
    (trace : Trace) (tuple : Tuple) (tag : M) (lambda : Q)
    (side : Usize) (values : Values) (arity : Arity) :
    @host_semantic.copy_endpoint_values _ {ops with op223 := f}
      trace tuple tag lambda side values arity =
    @host_semantic.copy_endpoint_values _ {ops with op223 := g}
      trace tuple tag lambda side values arity := by
  simp only [host_semantic.copy_endpoint_values,PV_CB_Op223TupleSupport.tuple,
    lift,bind_tc_ok,aspis_statement.logup.compress_tagged_tuple,
    array_agree ops f g agree]
  rfl
#print axioms array_agree
#print axioms endpoint
end R1Z.PV_CB_Op223Callsite
