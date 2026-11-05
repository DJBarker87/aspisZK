import NIM_NHY_COMBINED_IMPORT
import NHL_Tx1Model
set_option autoImplicit false
namespace NIS_DigestCarrier
open Aeneas Aeneas.Std Result

/-- Distinct emitted trait owners; the actual callback and byte carriers are
shared unchanged. This supplies no digest value or native caller law. -/
def toCaller {H : Type} (D : AdapterRw.aspis_core.digest.Digest32 H) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 H :=
  ⟨D.coremarkerCopyInst,D.digest⟩

def toAdapter {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) :
    AdapterRw.aspis_core.digest.Digest32 H :=
  ⟨D.coremarkerCopyInst,D.digest⟩

theorem adapter_roundtrip {H : Type} (D : AdapterRw.aspis_core.digest.Digest32 H) :
    toAdapter (toCaller D)=D := by cases D; rfl
theorem caller_roundtrip {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) :
    toCaller (toAdapter D)=D := by cases D; rfl

theorem callback {H : Type} (D : AdapterRw.aspis_core.digest.Digest32 H) :
    (toCaller D).digest=D.digest := rfl

#print axioms adapter_roundtrip
#print axioms caller_roundtrip
#print axioms callback
end NIS_DigestCarrier
