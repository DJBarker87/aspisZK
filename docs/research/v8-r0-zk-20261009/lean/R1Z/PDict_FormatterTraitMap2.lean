import R1Z.PDict_FormatterTraitMap
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterTraitMap2
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterTraitMap

def unFixed (b : ExternalTypes) (F : Type) (S O A : Type)
    (x : @digest.FixedOutput (types b F) S O A) : @digest.FixedOutput b S O A := by
  cases x with
  | mk update output finalize => exact @digest.FixedOutput.mk b S O A update output finalize

def unFixedCore (b : ExternalTypes) (F : Type) (S B A K KB KA O OA R : Type)
    (x : @digest.core_api.FixedOutputCore (types b F) S B A K KB KA O OA R) :
    @digest.core_api.FixedOutputCore b S B A K KB KA O OA R := by
  cases x with
  | mk update buffer output less nonzero finalize =>
    exact @digest.core_api.FixedOutputCore.mk b S B A K KB KA O OA R
      (unUpdate b F S B A update) (unBufferUser b F S K KB KA buffer)
      output less nonzero finalize

#print axioms unFixed
#print axioms unFixedCore
end R1Z.PDict_FormatterTraitMap2
