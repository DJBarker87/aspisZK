import R1Z.PV_CB_ProducerLimb
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerOffsets
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]
abbrev zero := AspisR1ProducerRelease47.field.M31.ZERO

theorem zero_valid : PV_CB_CanonicalM31.Valid zero := by
  unfold zero AspisR1ProducerRelease47.field.M31.ZERO
  change (0#u32).val < AspisCircleGroupOrder.P
  decide

theorem zero_limb : OffsetValid aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1.Zero := by
  trivial

theorem zero_cell (source : aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1) :
    OffsetValid (.Cell source zero) := zero_valid

/-- Both source offset branches have canonical results for any canonical
    tweak. This is a primitive source theorem, not a registry extraction. -/
theorem subtract (ops : ExternalFuns) (tweak : U32) (vt : PV_CB_CanonicalM31.Valid tweak) :
    ∃ offset, @aspis_core.field.M31.sub _ (ProverRwDictionaryScalar.selected ops) zero tweak = ok offset ∧
      PV_CB_CanonicalM31.Valid offset := by
  obtain ⟨offset,hr,hv,_⟩ := ProverCommitM31Ops48.sub_exact zero tweak zero_valid vt
  exact ⟨offset,hr,hv⟩

#print axioms zero_valid
#print axioms zero_limb
#print axioms zero_cell
#print axioms subtract
end R1Z.PV_CB_ProducerOffsets
