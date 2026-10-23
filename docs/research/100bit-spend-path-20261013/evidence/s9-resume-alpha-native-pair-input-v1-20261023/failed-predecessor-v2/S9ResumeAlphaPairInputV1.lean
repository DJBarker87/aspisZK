import S9ResumeAlphaSourceCanonicalV1
import S9ArrayTwoPrefixSourceV1
import S9ActualPairWideCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeAlphaPairInputV1
abbrev SW := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev NW := AspisR1S9ActualPairWideCanonicalV1.W
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical

def toNative (x : SW) : NW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def toNativeSlice (s : Slice SW) : Slice NW :=
  ⟨s.val.map toNative, by simpa using s.property⟩

theorem toNative_canonical (x : SW)
    (h : AspisR1S4ReaderEActualWideCanonicalV1.currentWideCanonical x) : Can (toNative x) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

private theorem successful_slice_read_mem {A : Type} (s : Slice A) (i : Usize) (v : A)
    (h : Slice.index_usize s i = .ok v) : v ∈ s.val := by
  unfold Slice.index_usize at h
  cases hr : s[i]? with
  | none => simp [hr] at h
  | some w =>
    have hi : s.val[i.val]? = some w := by simpa using hr
    have hm := List.mem_of_getElem? hi
    rw [hr] at h
    have he : w = v := Result.ok.inj h
    exact he ▸ hm

/-- Same strict resume output, exact finish_relation RangeTo2 operation and
coordinate-only carrier transport supply the native Pair alpha read contract.
The selected slice is obtained by the actual emitted source operation; no
slice-equality or challenge-canonicality premise is supplied. The enclosing
caller still has to bind its Pair slot to this same transported input. -/
theorem resume_finish_prefix_native_alpha_canonical
    (ops : AspisR1Stage2.ResumeOps) {H : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (variant : AspisR1Stage2.transport.Variant) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (selected : Slice SW)
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
      D bytes proof publicInput variant hash = .ok (.Ok (p,acc)))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW))
      p.alpha { «end» := 2#usize } = .ok selected) :
    ∀ (i : Usize) (v : NW), Slice.index_usize (toNativeSlice selected) i = .ok v → Can v := by
  obtain ⟨a0,a1,r0,r1,r2,halpha,hr0,hr1,h0,h1⟩ :=
    AspisR1S9ResumeAlphaSourceCanonicalV1.resume_success_alpha_sources_canonical
      ops D bytes proof publicInput variant hash p acc hresume
  have hslice := AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq
    p.alpha selected hselected
  subst selected
  intro i v hread
  have hm := successful_slice_read_mem _ i v hread
  rw [halpha] at hm
  change v ∈ [toNative a0,toNative a1] at hm
  simp only [List.mem_cons,List.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact toNative_canonical a0 h0
  · exact toNative_canonical a1 h1

#print axioms toNative_canonical
#print axioms resume_finish_prefix_native_alpha_canonical
end AspisR1S9ResumeAlphaPairInputV1
