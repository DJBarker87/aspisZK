import R1Z.PDict_FormatterTypeMaps
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterTraitMap
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps

def unUpdate (b : ExternalTypes) (F : Type) (S B A : Type)
    (x : @digest.core_api.UpdateCore (types b F) S B A) : @digest.core_api.UpdateCore b S B A := by
  cases x with
  | mk block update => exact @digest.core_api.UpdateCore.mk b S B A block update

def unSealed (b : ExternalTypes) (F : Type) (S : Type)
    (x : @block_buffer.sealed.Sealed (types b F) S) : @block_buffer.sealed.Sealed b S := by
  cases x with
  | mk inv split => exact @block_buffer.sealed.Sealed.mk b S inv split

def unBuffer (b : ExternalTypes) (F : Type) (S : Type)
    (x : @block_buffer.BufferKind (types b F) S) : @block_buffer.BufferKind b S := by
  cases x with
  | mk sealed => exact @block_buffer.BufferKind.mk b S (unSealed b F S sealed)

def unBufferUser (b : ExternalTypes) (F : Type) (S K B A : Type)
    (x : @digest.core_api.BufferKindUser (types b F) S K B A) : @digest.core_api.BufferKindUser b S K B A := by
  cases x with
  | mk block kind => exact @digest.core_api.BufferKindUser.mk b S K B A block (unBuffer b F K kind)

def unVariable (b : ExternalTypes) (F : Type) (S B A O OA K KB KA R : Type)
    (x : @digest.core_api.VariableOutputCore (types b F) S B A O OA K KB KA R) :
    @digest.core_api.VariableOutputCore b S B A O OA K KB KA R := by
  cases x with
  | mk trunc update output buffer less nonzero new finalize =>
    exact @digest.core_api.VariableOutputCore.mk b S B A O OA K KB KA R
      trunc (unUpdate b F S B A update) output (unBufferUser b F S K KB KA buffer)
      less nonzero new finalize

#print axioms unUpdate
#print axioms unSealed
#print axioms unBuffer
#print axioms unBufferUser
#print axioms unVariable
end R1Z.PDict_FormatterTraitMap
