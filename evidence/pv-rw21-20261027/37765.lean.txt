import R1Z.ProverRwFullFuns
import R1Z.ProverRw18ContextJoin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Arity16Endpoint
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Compression := ProverRw18ContextJoin.Compression

def Agree16 (f g : Compression) : Prop :=
  ∀ tag (values : Array U32 16#usize) lambda,
    f tag (Array.to_slice values) lambda=g tag (Array.to_slice values) lambda

theorem tuple (ops : ExternalFuns) (f g : Compression)
    (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1)
    (tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1) :
    @host_semantic.copy_tuple_values _ {ops with op223 := f} trace tuple =
      @host_semantic.copy_tuple_values _ {ops with op223 := g} trace tuple := rfl

/-- The only emitted op223 call consumes the fixed 16-limb tuple. All outer
Results, caller guards and mutable writeback remain in this statement. -/
theorem endpoint (ops : ExternalFuns) (f g : Compression) (h : Agree16 f g)
    (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1)
    (tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1)
    (tag : U32) (lambda : aspis_core.field.QM31) (side : Usize)
    (values : alloc.vec.Vec (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (arity : alloc.vec.Vec (Array Usize 2#usize)) :
    @host_semantic.copy_endpoint_values _ {ops with op223 := f} trace tuple tag lambda side values arity =
      @host_semantic.copy_endpoint_values _ {ops with op223 := g} trace tuple tag lambda side values arity := by
  unfold Agree16 at h
  simp only [host_semantic.copy_endpoint_values,ProverRw21Arity16Endpoint.tuple ops f g,
    lift,bind_tc_ok,aspis_statement.logup.compress_tagged_tuple,h]
  rfl

theorem function (ops : ExternalFuns) (f g : Compression) (h : Agree16 f g) :
    @host_semantic.copy_endpoint_values _ {ops with op223 := f} =
      @host_semantic.copy_endpoint_values _ {ops with op223 := g} := by
  funext trace tuple tag lambda side values arity
  exact endpoint ops f g h trace tuple tag lambda side values arity

#print axioms Agree16
#print axioms tuple
#print axioms endpoint
#print axioms function
end R1Z.ProverRw21Arity16Endpoint
