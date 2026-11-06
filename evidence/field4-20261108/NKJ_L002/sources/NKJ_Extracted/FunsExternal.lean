import NKJ_Extracted.Types
import NGA_SmallResult
set_option autoImplicit false
namespace NKJ_Extracted
open Aeneas Aeneas.Std Result

def fromCanonical (q : AspisR1SelectedMaskProbe.field.QM31) : field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toCanonical (q : field.QM31) : AspisR1SelectedMaskProbe.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def field.qm31_from_karatsuba_channel_sums
 (s : Array (Array U64 3#usize) 3#usize) : Result field.QM31 := do
 let q ← NGA_SmallResult.convert s
 ok (fromCanonical q)

theorem roundtrip (q : AspisR1SelectedMaskProbe.field.QM31) :
 toCanonical (fromCanonical q)=q := by cases q with | mk a b => cases a;cases b;rfl
#print axioms roundtrip
end NKJ_Extracted
