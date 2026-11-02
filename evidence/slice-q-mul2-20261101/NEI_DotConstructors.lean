import NEG_DotAssociation
set_option autoImplicit false
namespace NEI_DotConstructors
open Aeneas Aeneas.Std Result
abbrev D := FIo_Native.fast_pairing.canonical.Dot
abbrev E := FIo_Native.fast_pairing.EbyKDot
def zero : D := ⟨Array.repeat 4#usize 0#u64⟩
def initial : E := ⟨zero,zero,0#usize⟩
theorem dot_new : FIo_Native.fast_pairing.canonical.Dot.new=ok zero := by rfl
theorem eby_new : FIo_Native.fast_pairing.EbyKDot.new=ok initial := by rfl
/-- Full immutable-value frame counterpart to the native two-receiver test. -/
theorem left_frame (before : E) (row : Array U64 4#usize) :
 ({before with c0:=⟨row⟩} : E).c1=before.c1 ∧
 ({before with c0:=⟨row⟩} : E).count=before.count := ⟨rfl,rfl⟩
#print axioms dot_new
#print axioms eby_new
#print axioms left_frame
end NEI_DotConstructors
