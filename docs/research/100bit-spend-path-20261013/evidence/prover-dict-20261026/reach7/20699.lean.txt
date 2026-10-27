import R1Z.PDict_FormatterStoreMap
set_option autoImplicit false
namespace R1Z.PDict_FormatterTypeEquiv
open ProverRwFull PDict_FormatterTypeMaps PDict_FormatterStoreMap

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def lateEquiv (b : ExternalTypes) (F : Type) : @Late b ≃ @Late (types b F) where
  toFun := PDict_FormatterTypeMaps.late b F
  invFun := PDict_FormatterTypeMaps.unlate b F
  left_inv := PDict_FormatterTypeMaps.late_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms lateEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def traceEquiv (b : ExternalTypes) (F : Type) : @Trace b ≃ @Trace (types b F) where
  toFun := PDict_FormatterTypeMaps.trace b F
  invFun := PDict_FormatterTypeMaps.untrace b F
  left_inv := PDict_FormatterTypeMaps.trace_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms traceEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def compilationEquiv (b : ExternalTypes) (F : Type) : @Compilation b ≃ @Compilation (types b F) where
  toFun := PDict_FormatterTypeMaps.compilation b F
  invFun := PDict_FormatterTypeMaps.uncompilation b F
  left_inv := PDict_FormatterTypeMaps.compilation_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms compilationEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def linkEquiv (b : ExternalTypes) (F : Type) : @CopyLink b ≃ @CopyLink (types b F) where
  toFun := PDict_FormatterTypeMaps.link b F
  invFun := PDict_FormatterTypeMaps.unlink b F
  left_inv := PDict_FormatterTypeMaps.link_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms linkEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def timesEquiv (b : ExternalTypes) (F : Type) : @Times b ≃ @Times (types b F) where
  toFun := PDict_FormatterTypeMaps.times b F
  invFun := PDict_FormatterTypeMaps.untimes b F
  left_inv := PDict_FormatterTypeMaps.times_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms timesEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def pubEquiv (b : ExternalTypes) (F : Type) : @Public b ≃ @Public (types b F) where
  toFun := PDict_FormatterTypeMaps.pub b F
  invFun := PDict_FormatterTypeMaps.unpublic b F
  left_inv := PDict_FormatterTypeMaps.public_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms pubEquiv

/-- Structural carrier equivalence; native Formatter/world adequacy is separate. -/
def storeEquiv (b : ExternalTypes) (F : Type) : @Store b ≃ @Store (types b F) where
  toFun := PDict_FormatterStoreMap.store b F
  invFun := PDict_FormatterStoreMap.unstore b F
  left_inv := PDict_FormatterStoreMap.store_roundtrip b F
  right_inv := by intro x; cases x <;> rfl
#print axioms storeEquiv
end R1Z.PDict_FormatterTypeEquiv
