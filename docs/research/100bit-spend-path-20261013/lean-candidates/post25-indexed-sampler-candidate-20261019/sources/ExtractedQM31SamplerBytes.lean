import AspisR1Qm31SamplerIndex.Funs

/-!
Actual byte-assembly loop of the extracted QM31 sampler. The target words use
exactly the primitive U32 little-endian decoder called by the generated body.
No byte-rank model or division theorem is introduced here.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerBytes
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1Qm31SamplerIndex

abbrev Block := Array U8 32#usize
abbrev Words := Array U32 8#usize

def byteAt (block : Block) (i : Fin 32) : U8 :=
  block.val[i.val]'(by have := block.property; change block.val.length = 32 at this; omega)

def byteWord (block : Block) (j : Fin 8) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize
    [byteAt block ⟨4 * j.val, by omega⟩,
     byteAt block ⟨4 * j.val + 1, by omega⟩,
     byteAt block ⟨4 * j.val + 2, by omega⟩,
     byteAt block ⟨4 * j.val + 3, by omega⟩])

def byteWords (block : Block) : Words :=
  ⟨List.ofFn (byteWord block), by simp⟩

def wordAt (rank : Words) (j : Fin 8) : U32 :=
  rank.val[j.val]'(by have := rank.property; change rank.val.length = 8 at this; omega)

theorem wordAt_byteWords (block : Block) (j : Fin 8) :
    wordAt (byteWords block) j = byteWord block j := by
  simp only [wordAt, byteWords, List.getElem_ofFn]

private theorem index32 (block : Block) (i : Usize) (hi : i.val < 32) :
    Array.index_usize block i = ok (byteAt block ⟨i.val, hi⟩) := by
  have hb : i.val < block.length := by
    have := block.property
    change block.val.length = 32 at this
    change i.val < block.val.length
    omega
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists (Array.index_usize_spec block i hb)
  simpa only [byteAt] using hx.trans (congrArg Result.ok hval)

/-- One actual iteration succeeds with exactly the source word and next index. -/
theorem body_step (block : Block) (rank : Words) (i : Usize) (hi : i.val < 8) :
    ∃ next : Usize,
      sampler.qm31_digits_loop0.body block rank i =
        ok (cont (rank.set i (byteWord block ⟨i.val, hi⟩), next)) ∧
      next.val = i.val + 1 := by
  have hguard : i < 8#usize := by scalar_tac
  have hmax : 32 ≤ Usize.max := by scalar_tac
  obtain ⟨start, hmul, hstart⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := 4#usize) (y := i) (by scalar_tac))
  have hs : start.val = 4 * i.val := by simpa using hstart
  obtain ⟨p1, ha1, hp1⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
  obtain ⟨p2, ha2, hp2⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
  obtain ⟨p3, ha3, hp3⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := start) (y := 3#usize) (by scalar_tac))
  have hv1 : p1.val = 4 * i.val + 1 := by simpa [hs] using hp1
  have hv2 : p2.val = 4 * i.val + 2 := by simpa [hs] using hp2
  have hv3 : p3.val = 4 * i.val + 3 := by simpa [hs] using hp3
  have hidx0 := index32 block start (by omega)
  have hidx1 := index32 block p1 (by omega)
  have hidx2 := index32 block p2 (by omega)
  have hidx3 := index32 block p3 (by omega)
  have hib : i.val < rank.length := by
    have := rank.property
    change rank.val.length = 8 at this
    change i.val < rank.val.length
    omega
  obtain ⟨rank', hup, hrank⟩ := WP.spec_imp_exists
    (Array.update_spec rank i (byteWord block ⟨i.val, hi⟩) hib)
  have hu : Array.update rank i (byteWord block ⟨i.val, hi⟩) =
      ok (rank.set i (byteWord block ⟨i.val, hi⟩)) :=
    hup.trans (congrArg Result.ok hrank)
  obtain ⟨next, hn, hnext⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  refine ⟨next, ?_, by simpa using hnext⟩
  simp only [sampler.qm31_digits_loop0.body, if_pos hguard, hmul,
    bind_tc_ok, hidx0, ha1, hidx1, ha2, hidx2, ha3, hidx3, lift]
  have hw : core.num.U32.from_le_bytes (Array.make 4#usize
      [byteAt block ⟨start.val, by omega⟩,
       byteAt block ⟨p1.val, by omega⟩,
       byteAt block ⟨p2.val, by omega⟩,
       byteAt block ⟨p3.val, by omega⟩]) = byteWord block ⟨i.val, hi⟩ := by
    simp only [byteWord, hs, hv1, hv2, hv3]
  rw [hw, hu]
  simp only [bind_tc_ok, hn]


/-- Every position already visited has its exact source word. -/
def PrefixCorrect (block : Block) (rank : Words) (i : Usize) : Prop :=
  ∀ j : Fin 8, j.val < i.val → wordAt rank j = byteWord block j

theorem wordAt_set (rank : Words) (i : Usize) (x : U32) (j : Fin 8) :
    wordAt (rank.set i x) j = if i.val = j.val then x else wordAt rank j := by
  simp only [wordAt, Aeneas.Std.Array.set_val_eq, List.getElem_set]

private theorem words_eq_of_all (block : Block) (rank : Words)
    (h : ∀ j : Fin 8, wordAt rank j = byteWord block j) :
    rank = byteWords block := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [rank.property, (byteWords block).property])
  intro n hn hm
  have hn8 : n < 8 := by
    have := rank.property
    change rank.val.length = 8 at this
    omega
  exact (h ⟨n, hn8⟩).trans (wordAt_byteWords block ⟨n, hn8⟩).symm

/-- Totality from a bounded index and correct already-visited coordinates.
The measure is the number of remaining source words, not a concrete unroll. -/
theorem loop0_correct (block : Block) (rank : Words) (i : Usize)
    (hi : i.val ≤ 8) (hp : PrefixCorrect block rank i) :
    sampler.qm31_digits_loop0 block rank i = ok (byteWords block) := by
  have hs : WP.spec (sampler.qm31_digits_loop0 block rank i)
      (fun result => result = byteWords block) := by
    unfold sampler.qm31_digits_loop0
    refine loop.spec_decr_nat
      (fun s : Words × Usize => 8 - s.2.val)
      (fun s => s.2.val ≤ 8 ∧ PrefixCorrect block s.1 s.2)
      (fun result : Words => result = byteWords block)
      (fun s : Words × Usize => sampler.qm31_digits_loop0.body block s.1 s.2)
      (rank, i) ?_ ⟨hi, hp⟩
    rintro ⟨rank, i⟩ ⟨hi, hp⟩
    change i.val ≤ 8 at hi
    change ∀ j : Fin 8, j.val < i.val → wordAt rank j = byteWord block j at hp
    by_cases hlt : i.val < 8
    · obtain ⟨next, hbody, hnext⟩ := body_step block rank i hlt
      rw [hbody, WP.spec_ok]
      change (next.val ≤ 8 ∧
        PrefixCorrect block (rank.set i (byteWord block ⟨i.val, hlt⟩)) next) ∧
        8 - next.val < 8 - i.val
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro j hj
      rw [wordAt_set]
      by_cases heq : i.val = j.val
      · rw [if_pos heq]
        exact congrArg (byteWord block) (Fin.ext heq)
      · rw [if_neg heq]
        exact hp j (by omega)
    · have hguard : ¬ i < 8#usize := by scalar_tac
      simp only [sampler.qm31_digits_loop0.body, if_neg hguard, WP.spec_ok]
      apply words_eq_of_all
      intro j
      exact hp j (by omega)
  obtain ⟨result, hresult, heq⟩ := WP.spec_imp_exists hs
  exact hresult.trans (congrArg Result.ok heq)

/-- The actual initial assembly loop overwrites all eight coordinates. -/
theorem loop0_total (block : Block) (rank : Words) :
    sampler.qm31_digits_loop0 block rank 0#usize = ok (byteWords block) := by
  apply loop0_correct block rank 0#usize (by decide)
  intro j hj
  have hzero : (0#usize).val = 0 := by decide
  omega

theorem assemble_total (block : Block) :
    sampler.qm31_digits_loop0 block (Array.repeat 8#usize 0#u32) 0#usize =
      ok (byteWords block) := loop0_total block _

#print axioms wordAt_byteWords
#print axioms body_step
#print axioms wordAt_set
#print axioms loop0_correct
#print axioms loop0_total
#print axioms assemble_total

end AspisR1.ExtractedQM31SamplerBytes
