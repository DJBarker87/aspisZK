import NDH_Reference.Funs
import NDH_CanonicalWide
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace NDH_Decode8
open Aeneas Aeneas.Std Result AspisR1Post25Sampler

def digit (d : Array U32 8#usize) (i : Fin 8) : U32 :=
  d.val[i.val]'(by have := d.property; change d.val.length=8 at this; omega)

def asWide (d : Array U32 8#usize) : field.WideExact :=
  ⟨⟨⟨digit d 0,digit d 1⟩,⟨digit d 2,digit d 3⟩⟩,
   ⟨⟨digit d 4,digit d 5⟩,⟨digit d 6,digit d 7⟩⟩⟩

theorem reference (d : Array U32 8#usize)
    (canonical : ∀ i : Fin 8, (digit d i).val < 2147483647) :
    (do let values ← NDH_Reference.pack8_ref d
        ok (asWide values)) = sampler.decode8 d := by
  have i0 : Array.index_usize d 0#usize = ok (digit d 0) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 0#usize (by decide)
  have i1 : Array.index_usize d 1#usize = ok (digit d 1) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 1#usize (by decide)
  have i2 : Array.index_usize d 2#usize = ok (digit d 2) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 2#usize (by decide)
  have i3 : Array.index_usize d 3#usize = ok (digit d 3) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 3#usize (by decide)
  have i4 : Array.index_usize d 4#usize = ok (digit d 4) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 4#usize (by decide)
  have i5 : Array.index_usize d 5#usize = ok (digit d 5) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 5#usize (by decide)
  have i6 : Array.index_usize d 6#usize = ok (digit d 6) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 6#usize (by decide)
  have i7 : Array.index_usize d 7#usize = ok (digit d 7) := by
    simpa [digit] using R1Z.ProverCommitArrayIndex25.array_index_usize_ok d 7#usize (by decide)
  simp only [NDH_Reference.pack8_ref, bind_tc_ok, sampler.decode8,
    i0,i1,i2,i3,i4,i5,i6,i7,field.CM31.new,field.WideExact.new]
  rw [NDH_CanonicalWide.canonical_success _ (canonical 0) (canonical 1) (canonical 2) (canonical 3)]
  simp only [bind_tc_ok]
  rw [NDH_CanonicalWide.canonical_success _ (canonical 4) (canonical 5) (canonical 6) (canonical 7)]
  rfl

#print axioms reference
end NDH_Decode8
