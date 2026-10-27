import R1Z.PV_CB_ProducerLocalSelected
import R1Z.PV_CB_Op223Callsite
import R1Z.PV_CB_ReachBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerLocalCallsite
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb PV_CB_Op223CellSupport
variable [ExternalTypes]

/-- Exact caller transport requires callback agreement only for numerically
    canonical arrays produced by this trace/tuple. This does not supply that
    open native callback agreement. All failure Results remain unchanged. -/
theorem endpoint (ops : ExternalFuns) (f g : Compressor)
    (trace : Trace) (tuple : PV_CB_ProducerTuple.Tuple)
    (vt : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace) tuple.limbs)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid tuple.limbs)
    (tag : U32) (lambda : Q)
    (agree : ∀ values : Array U32 16#usize,
      PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values →
      f tag (Array.to_slice values) lambda = g tag (Array.to_slice values) lambda)
    (side : Usize) (values : PV_CB_Op223Callsite.Values) (arity : PV_CB_Op223Callsite.Arity) :
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := f}
      trace tuple tag lambda side values arity =
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := g}
      trace tuple tag lambda side values arity := by
  simp only [host_semantic.copy_endpoint_values,PV_CB_Op223TupleSupport.tuple,
    lift,bind_tc_ok,aspis_statement.logup.compress_tagged_tuple,aspis_core.field.QM31.add]
  split
  · rfl
  · apply PV_CB_ReachBind.congr
    intro a ha
    apply PV_CB_ReachBind.congr
    intro i hi
    split
    · rfl
    · apply PV_CB_ReachBind.congr
      intro slot hslot
      apply PV_CB_ReachBind.congr
      intro pair hp
      rcases pair with ⟨a1,index_mut_back⟩
      apply PV_CB_ReachBind.congr
      intro i1 hi1
      apply PV_CB_ReachBind.congr
      intro pair2 hp2
      rcases pair2 with ⟨unused,index_mut_back1⟩
      apply PV_CB_ReachBind.congr
      intro result hr
      cases result with
      | Err err => rfl
      | Ok produced =>
        have valid := PV_CB_ProducerLocalSelected.tuple ops trace tuple vt vo produced hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        congr 1
        exact agree produced valid
#print axioms endpoint
end R1Z.PV_CB_ProducerLocalCallsite
