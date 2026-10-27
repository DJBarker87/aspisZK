import R1Z.PDict_Static222_02
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output`. -/
theorem erase_48 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output (types base F) (selected base F ops) = @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output base ops := by
  delta typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output
  all_goals rfl
#print axioms erase_48

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar`. -/
theorem erase_49 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar base ops := by
  delta typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar
  all_goals rfl
#print axioms erase_49

/-- Carrier transport candidate for `std.path.Path.Insts.CoreConvertAsRefPath`. -/
theorem erase_51 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @std.path.Path.Insts.CoreConvertAsRefPath (types base F) (selected base F ops) = @std.path.Path.Insts.CoreConvertAsRefPath base ops := by
  delta std.path.Path.Insts.CoreConvertAsRefPath
  all_goals rfl
#print axioms erase_51

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.sync_directory`. -/
theorem erase_52 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.sync_directory (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.sync_directory base ops := by
  exact PDict_FormatterIOMap.sync_directory base F ops
#print axioms erase_52

/-- Carrier transport candidate for `std.path.PathBuf.Insts.CoreConvertAsRefPath`. -/
theorem erase_53 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @std.path.PathBuf.Insts.CoreConvertAsRefPath (types base F) (selected base F ops) = @std.path.PathBuf.Insts.CoreConvertAsRefPath base ops := by
  delta std.path.PathBuf.Insts.CoreConvertAsRefPath
  all_goals rfl
#print axioms erase_53

/-- Carrier transport candidate for `aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone`. -/
theorem erase_57 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone (types base F) (selected base F ops) = @aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone base ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_57

/-- Carrier transport candidate for `aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy`. -/
theorem erase_58 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy base ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy
  first | rfl | (try simp only [erase_57 base F ops]; all_goals rfl)
#print axioms erase_58

/-- Carrier transport candidate for `aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32`. -/
theorem erase_59 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base F) (selected base F ops) = @aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 base ops := by
  delta aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
  first | rfl | (try simp only [erase_58 base F ops]; all_goals rfl)
#print axioms erase_59

/-- Carrier transport candidate for `aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31`. -/
theorem erase_60 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 (types base F) (selected base F ops) = @aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 base ops := by
  delta aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
  all_goals rfl
#print axioms erase_60

/-- Carrier transport candidate for `aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone`. -/
theorem erase_61 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone (types base F) (selected base F ops) = @aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone base ops := by
  delta aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_61

/-- Carrier transport candidate for `Array.Insts.ZeroizeZeroize`. -/
theorem erase_62 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @Array.Insts.ZeroizeZeroize (types base F) (selected base F ops) = @Array.Insts.ZeroizeZeroize base ops := by
  delta Array.Insts.ZeroizeZeroize
  all_goals rfl
#print axioms erase_62

/-- Carrier transport candidate for `alloc.vec.Vec.Insts.CoreDefaultDefault`. -/
theorem erase_63 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @alloc.vec.Vec.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @alloc.vec.Vec.Insts.CoreDefaultDefault base ops := by
  delta alloc.vec.Vec.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_63
end R1Z.PDict_Static222
