import R1Z.PDict_Publication
set_option autoImplicit false
namespace R1Z.PDict_DigestNew
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
def digestNew
  {D : Type} {Clause0_Clause1_OutputSize : Type}
  {Clause0_Clause1_Clause0_ArrayType : Type} (FixedOutputInst :
  digest.FixedOutput D Clause0_Clause1_OutputSize
  Clause0_Clause1_Clause0_ArrayType) (coredefaultDefaultInst :
  core.default.Default D) (UpdateInst : digest.Update D) (HashMarkerInst :
  digest.digest.HashMarker D) :
  Result D
  := do
  coredefaultDefaultInst.default

end R1Z.PDict_DigestNew
