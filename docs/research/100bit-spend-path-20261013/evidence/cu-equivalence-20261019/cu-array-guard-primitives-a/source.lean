import AspisR1CuArraySource.Types

/-! Concrete safe-domain interpretation of the three unsafe library primitives
used by Guard.push_unchecked. This is NOT their Rust-source admission theorem.
The consuming proof establishes in-bounds indexing and no-overflow addition;
it cannot infer correctness of the source primitives from these definitions. -/
set_option autoImplicit false
namespace AspisR1CuArraySource
open Aeneas Aeneas.Std Result

def core.slice.Slice.get_unchecked_mut
    {T I Output : Type}
    (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) Output)
    (buffer : Slice T) (index : I) : Result (Output × (Output → Slice T)) :=
  inst.index_mut index buffer

def core.mem.maybe_uninit.MaybeUninit.write {T : Type}
    (_cell : core.mem.maybe_uninit.MaybeUninit T) (item : T) :
    Result (T × (T → core.mem.maybe_uninit.MaybeUninit T)) :=
  .ok (item,fun value => some value)

def core.num.Usize.unchecked_add (left right : Usize) : Result Usize :=
  UScalar.add left right

#print axioms core.slice.Slice.get_unchecked_mut
#print axioms core.mem.maybe_uninit.MaybeUninit.write
#print axioms core.num.Usize.unchecked_add
end AspisR1CuArraySource
