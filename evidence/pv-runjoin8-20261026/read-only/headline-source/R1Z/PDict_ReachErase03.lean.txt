import R1Z.PDict_ReachErase02
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output`. -/
theorem erase_48 (ops other : ExternalFuns) :
    @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output _ (replace ops other) = @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output _ ops := by
  delta typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output
  all_goals rfl
#print axioms erase_48

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar`. -/
theorem erase_49 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar _ (replace ops other) = @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar _ ops := by
  delta typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar
  all_goals rfl
#print axioms erase_49

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path`. -/
theorem erase_50 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path _ (replace ops other) = @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path _ ops := by
  delta aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
  first | rfl | (try simp only [erase_0 ops other, erase_1 ops other, erase_2 ops other, erase_3 ops other, erase_4 ops other, erase_5 ops other, erase_6 ops other, erase_8 ops other, erase_7 ops other, erase_9 ops other, erase_11 ops other, erase_10 ops other, erase_45 ops other, erase_37 ops other, erase_38 ops other, erase_12 ops other, erase_15 ops other, erase_21 ops other, erase_24 ops other, erase_46 ops other, erase_39 ops other, erase_40 ops other, erase_47 ops other, erase_16 ops other, erase_19 ops other, erase_20 ops other, erase_25 ops other, erase_41 ops other, erase_42 ops other, erase_43 ops other, erase_48 ops other, erase_26 ops other, erase_30 ops other, erase_29 ops other, erase_44 ops other, erase_49 ops other]; all_goals rfl)
#print axioms erase_50

/-- Full symbolic source-function equality for `std.path.Path.Insts.CoreConvertAsRefPath`. -/
theorem erase_51 (ops other : ExternalFuns) :
    @std.path.Path.Insts.CoreConvertAsRefPath _ (replace ops other) = @std.path.Path.Insts.CoreConvertAsRefPath _ ops := by
  delta std.path.Path.Insts.CoreConvertAsRefPath
  all_goals rfl
#print axioms erase_51

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.sync_directory`. -/
theorem erase_52 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.sync_directory _ (replace ops other) = @aspis_prover.state_only_entropy.sync_directory _ ops := by
  delta aspis_prover.state_only_entropy.sync_directory
  first | rfl | (try simp only [erase_1 ops other, erase_51 ops other]; all_goals rfl)
#print axioms erase_52

/-- Full symbolic source-function equality for `std.path.PathBuf.Insts.CoreConvertAsRefPath`. -/
theorem erase_53 (ops other : ExternalFuns) :
    @std.path.PathBuf.Insts.CoreConvertAsRefPath _ (replace ops other) = @std.path.PathBuf.Insts.CoreConvertAsRefPath _ ops := by
  delta std.path.PathBuf.Insts.CoreConvertAsRefPath
  all_goals rfl
#print axioms erase_53

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible`. -/
theorem erase_54 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ (replace ops other) = @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible _ ops := by
  delta aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  first | rfl | (try simp only [erase_50 ops other, erase_52 ops other, erase_53 ops other]; all_goals rfl)
#print axioms erase_54

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve`. -/
theorem erase_55 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ (replace ops other) = @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops := by
  delta aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  first | rfl | (try simp only [erase_54 ops other]; all_goals rfl)
#print axioms erase_55

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore`. -/
theorem erase_56 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ (replace ops other) = @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ ops := by
  delta aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
  first | rfl | (try simp only [erase_55 ops other]; all_goals rfl)
#print axioms erase_56

/-- Full symbolic source-function equality for `aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone`. -/
theorem erase_57 (ops other : ExternalFuns) :
    @aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone _ (replace ops other) = @aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone _ ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_57

/-- Full symbolic source-function equality for `aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy`. -/
theorem erase_58 (ops other : ExternalFuns) :
    @aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy _ (replace ops other) = @aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy _ ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy
  first | rfl | (try simp only [erase_57 ops other]; all_goals rfl)
#print axioms erase_58

/-- Full symbolic source-function equality for `aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32`. -/
theorem erase_59 (ops other : ExternalFuns) :
    @aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 _ (replace ops other) = @aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 _ ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
  first | rfl | (try simp only [erase_58 ops other]; all_goals rfl)
#print axioms erase_59

/-- Full symbolic source-function equality for `aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31`. -/
theorem erase_60 (ops other : ExternalFuns) :
    @aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 _ (replace ops other) = @aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 _ ops := by
  delta aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
  all_goals rfl
#print axioms erase_60

/-- Full symbolic source-function equality for `aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone`. -/
theorem erase_61 (ops other : ExternalFuns) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone _ (replace ops other) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone _ ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_61

/-- Full symbolic source-function equality for `Array.Insts.ZeroizeZeroize`. -/
theorem erase_62 (ops other : ExternalFuns) :
    @Array.Insts.ZeroizeZeroize _ (replace ops other) = @Array.Insts.ZeroizeZeroize _ ops := by
  delta Array.Insts.ZeroizeZeroize
  all_goals rfl
#print axioms erase_62

/-- Full symbolic source-function equality for `alloc.vec.Vec.Insts.CoreDefaultDefault`. -/
theorem erase_63 (ops other : ExternalFuns) :
    @alloc.vec.Vec.Insts.CoreDefaultDefault _ (replace ops other) = @alloc.vec.Vec.Insts.CoreDefaultDefault _ ops := by
  delta alloc.vec.Vec.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_63
end R1Z.PDict_ReachErase
