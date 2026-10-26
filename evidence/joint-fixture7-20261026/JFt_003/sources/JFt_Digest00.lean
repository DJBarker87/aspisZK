import JFu_PublicDigest00
import JFu_DigestSliceCanonical
import JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFt_Digest00
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [71235157#u32,561336479#u32,2021715933#u32,831357912#u32,593948515#u32,110335229#u32,1732475008#u32,949858646#u32]

/-- Only this32-byte canonical cell is reduced; the public buffer stays opaque. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest JFu_PublicDigest00.window=ok (.Ok value) := by rfl

theorem selected : JFu_PublicRange.segment 112 32 (by decide)=JFu_PublicDigest00.window := by
  apply Subtype.ext
  exact JFu_PublicDigest00.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment 112 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : JFu_DigestCanonical.Canonical value :=
  JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.JFt_Digest00
