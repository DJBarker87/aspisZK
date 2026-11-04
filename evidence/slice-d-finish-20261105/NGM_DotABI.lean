import NFG_PushRoot
import NGM_ArrayFour
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_DotABI
open Aeneas Aeneas.Std Result
abbrev Dot := FIo_Native.fast_pairing.EbyKDot
/-- Typed field projection. This is not a byte cast or representation axiom. -/
structure Words where
 left : Array U64 4#usize
 right : Array U64 4#usize
 count : Usize

def read (dot : Dot) : Words := ⟨dot.c0.sums,dot.c1.sums,dot.count⟩
def make (words : Words) : Dot := ⟨⟨words.left⟩,⟨words.right⟩,words.count⟩
theorem make_read (dot : Dot) : make (read dot)=dot := by
 cases dot with | mk a b count => cases a;cases b;rfl
theorem read_make (words : Words) : read (make words)=words := by cases words;rfl
theorem read_injective : Function.Injective read := by
 intro a b same
 have equal := congrArg make same
 simpa only [make_read] using equal

def overwrite (_ : Dot) (words : Words) : Dot := make words

theorem overwrite_exact (before after : Dot) : overwrite before (read after)=after := make_read after

/-- One full child reply and mutation; a rejection has no invented index
increment. The concrete per-window native association supplies this cut. -/
def stepResult (updated : Dot) (index : Usize) (reply : core.result.Result Unit Unit) :
 core.result.Result (Dot × Usize) AspisR1Stage2.verifier.Error :=
 match reply with
 | .Ok () => .Ok (updated,Usize.wrapping_add index 1#usize)
 | .Err () => .Err .Parse

theorem step_error (updated : Dot) (index : Usize) :
 stepResult updated index (.Err ())=.Err .Parse := rfl

theorem step_ok (updated : Dot) (index : Usize) :
 stepResult updated index (.Ok ())=.Ok (updated,Usize.wrapping_add index 1#usize) := rfl
#print axioms make_read
#print axioms read_make
#print axioms read_injective
#print axioms overwrite_exact
#print axioms step_error
#print axioms step_ok
end AspisR1.NGM_DotABI
end
