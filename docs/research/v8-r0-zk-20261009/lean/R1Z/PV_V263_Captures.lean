import R1Z.ProverRwFullFuns
import R1Z.PV_V263_Family
/-! Exact deployed callback captures and the pool's second range layer.
These equations retain the FULL source Result; they assert no success,
termination, runtime effect lifting, terminal value, or callback totality. -/
set_option autoImplicit false
namespace R1Z.PV_V263_Captures
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Source order is lane lookup, then encoder on the actual captured tuple. -/
theorem commitment (domain : host_commitment.EncodingDomain)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (lanes : Slice Usize) (i : Usize) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      (domain,messages,variant,lanes) i =
    (do let lane ← Slice.index_usize lanes i
        host_commitment.encode_commitment_lane domain messages variant lane) := rfl

/-- The digest type is a capture-type parameter, not a replacement oracle. -/
theorem sumcheck {H T : Type} (digest : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle T) (oracle : T)
    (point : Array aspis_core.field.QM31 10#usize) (round assignments i : Usize) :
    host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
      digest oi (oracle,point,round,assignments) i =
    host_sumcheck.evaluate_assignment oi oracle point round assignments i := rfl

/-- ordered_families is called with n=THREADS, independently of the host item
count. Each pool family therefore contains exactly one host-work family. -/
theorem pool_range (k : Nat) :
    PV_RunJoin_WorkRange35.start 16 k = k ∧ PV_RunJoin_WorkRange35.width 16 k = 1 := by
  simp only [PV_RunJoin_WorkRange35.start,PV_RunJoin_WorkRange35.width,
    show 16/16=1 from rfl,show 16%16=0 from rfl,Nat.one_mul,Nat.min_zero,
    Nat.add_zero,Nat.not_lt_zero,if_false]
  constructor <;> trivial

theorem pool_indices (k : Nat) : PV_V263_Family.indices 16 k = [k] := by
  unfold PV_V263_Family.indices
  rw [(pool_range k).1,(pool_range k).2]
  simp only [List.range'_succ,List.range'_zero,List.nil_append]

#print axioms commitment
#print axioms sumcheck
#print axioms pool_range
#print axioms pool_indices
end R1Z.PV_V263_Captures
