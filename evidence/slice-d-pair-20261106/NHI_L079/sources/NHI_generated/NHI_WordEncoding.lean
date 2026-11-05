import NHI_TensorExactCell
set_option autoImplicit false
namespace NHI_WordEncoding
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Word := Array U32 4#usize

def words (q : NQ) : Word := Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def record (w : Word) : NQ :=
 ⟨⟨NHI_ScalarDomain.pick w 0 (by decide),NHI_ScalarDomain.pick w 1 (by decide)⟩,
  ⟨NHI_ScalarDomain.pick w 2 (by decide),NHI_ScalarDomain.pick w 3 (by decide)⟩⟩

theorem roundtrip (q : NQ) : record (words q)=q := rfl

theorem injective : Function.Injective words := by
 intro x y same
 have h := congrArg record same
 simpa only [roundtrip] using h

def encode (s : Slice NQ) : Slice Word := ⟨s.val.map words,by simpa only [List.length_map] using s.property⟩

theorem put (s : Slice NQ) (i : Nat) (x : NQ) :
 encode (NHI_SliceCells.put s i x)=NHI_SliceCells.put (encode s) i (words x) := by
 apply Subtype.ext
 exact List.map_set

def array (s : Slice NQ) (size : s.val.length=64) : Array Word 64#usize :=
 ⟨s.val.map words,by rw [List.length_map,size] <;> rfl⟩

#print axioms roundtrip
#print axioms injective
#print axioms put
end NHI_WordEncoding
