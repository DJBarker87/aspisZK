import NDO_JGe_Payload27
import PSem_Values
import MultiproofConeByteEquality
set_option autoImplicit false
namespace AspisR1.JGp_ValuesIdentity
open Aeneas Aeneas.Std Result

theorem source (initial out : Slice U8)
    (run : AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored initial=ok (.Ok (),out)) :
    out=JGe_Payload27.value := by
  have actual := PSem_Values.source_expansion _ _ _ run
  have retained := PSem_Values.source_expansion _ _ _ JGe_Payload27.source
  exact Subtype.ext (MultiproofConeByteEquality.bytes_injective (actual.trans retained.symm))
#print axioms source
end AspisR1.JGp_ValuesIdentity
