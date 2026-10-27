import R1Z.PV_CB_Op223TupleProducerFuns
import R1Z.PV_CB_CanonicalM31Ops
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerScalar
open Aeneas Aeneas.Std Result
namespace S
abbrev sub := PV_CB_ShippedOp223Tuple.aspis_core.field.M31.sub
abbrev zero := PV_CB_ShippedOp223Tuple.aspis_core.field.M31.ZERO
abbrev tweak := PV_CB_ShippedOp223Tuple.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
end S

theorem sub (a b : U32) : S.sub a b = AspisR1ProducerRelease47.field.M31.sub a b := by
  simp only [S.sub,PV_CB_ShippedOp223Tuple.aspis_core.field.M31.sub,
    AspisR1ProducerRelease47.field.M31.sub,
    PV_CB_ShippedOp223Tuple.aspis_core.field.P,AspisR1ProducerRelease47.field.P,
    lift,bind_tc_ok]

theorem canonical (a b : U32) (va : PV_CB_CanonicalM31.Valid a) (vb : PV_CB_CanonicalM31.Valid b) :
    ∃ out, S.sub a b = ok out ∧ PV_CB_CanonicalM31.Valid out := by
  obtain ⟨out,hr,vr,_⟩ := ProverCommitM31Ops48.sub_exact a b va vb
  exact ⟨out,(sub a b).trans hr,vr⟩

theorem zero_valid : PV_CB_CanonicalM31.Valid S.zero := by
  unfold S.zero PV_CB_ShippedOp223Tuple.aspis_core.field.M31.ZERO
  change (0#u32).val < AspisCircleGroupOrder.P
  decide

theorem tweak_valid : PV_CB_CanonicalM31.Valid S.tweak := by
  unfold S.tweak PV_CB_ShippedOp223Tuple.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
  change (1095962629#u32).val < AspisCircleGroupOrder.P
  decide
#print axioms sub
#print axioms canonical
#print axioms zero_valid
#print axioms tweak_valid
end R1Z.PV_CB_TupleProducerScalar
