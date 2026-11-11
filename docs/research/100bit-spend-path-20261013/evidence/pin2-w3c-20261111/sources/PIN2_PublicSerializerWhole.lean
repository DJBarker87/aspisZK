import PIN2_PublicBytesRefinement

/-! PIN2 W3c (2026-11-11): the PIN2 counterpart of `PublicSerializerWhole431`.

`PublicSerializerWhole431` proves, for the frozen 4bb3b3f extraction, that the
generated `r0::Public::public_bytes` is a step program (`source_eq_program`) and
that every successful run fixes all bytes and proves every serialized field word
canonical (`source_success`).  For the PIN2 re-extraction (`PIN2_NEWGATE_r0`,
Stream C emission PCXQ_E001 at W1 source 271869c946d) the step program and the
byte half are W3b's `PIN2_PublicBytesRefinement.source_eq_program` /
`program_success`; this module adds the canonicality half and states the PIN2
`source_success` in the release form.  The release module stays valid for the
frozen extraction and is still imported (through W3b's modules) for its generic
helpers `bind_success`, `push_success` and the 4.31 field/frontier encoders. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicSerializer.PIN2Whole
open FieldsRefinement431

abbrev Public := AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Step := AspisR1.PIN2_PublicBytesRefinement.Step

/-- Field words written by each PIN2 instruction (raw/byte/index write none). -/
def stepWords : Step → List Field
  | .byte _ => []
  | .words s => s.val
  | .frontier f => (Frontier431.rows f).flatMap (fun s => s.val)
  | .index _ => []
  | .raw _ => []

/-- A successful run of the PIN2 instruction program proves every serialized
field word canonical (read off the same transported helper successes). -/
theorem program_canonical (ss : List Step) (out out' : ByteVec)
    (h : AspisR1.PIN2_PublicBytesRefinement.program ss out = ok (.Ok out')) :
    canonical (ss.flatMap stepWords) := by
  induction ss generalizing out with
  | nil => simp [canonical]
  | cons s ss ih =>
    cases s with
    | byte b =>
      obtain ⟨out1, _, hr⟩ := Whole431.bind_success _ _ _ h
      simpa only [List.flatMap_cons, stepWords, List.nil_append] using ih out1 hr
    | index n =>
      obtain ⟨out1, _, hr⟩ := Whole431.bind_success _ _ _ h
      simpa only [List.flatMap_cons, stepWords, List.nil_append] using ih out1 hr
    | raw a =>
      obtain ⟨out1, _, hr⟩ := Whole431.bind_success _ _ _ h
      simpa only [List.flatMap_cons, stepWords, List.nil_append] using ih out1 hr
    | words s =>
      obtain ⟨out1, hf, hr⟩ := AspisR1.PIN2_PublicBytesRefinement.nextPublic_success _ _ _ h
      have hf := AspisR1.PIN2_SerializerTransport.fields_success out out1 s hf
      have hi := ih out1 hr
      intro x hx
      simp only [List.flatMap_cons, stepWords, List.mem_append] at hx
      exact hx.elim (hf.1 x) (hi x)
    | frontier f =>
      obtain ⟨out1, hf, hr⟩ := AspisR1.PIN2_PublicBytesRefinement.nextPublic_success _ _ _ h
      have hf := AspisR1.PIN2_SerializerTransport.frontier_success out out1 f hf
      have hi := ih out1 hr
      intro x hx
      simp only [List.flatMap_cons, stepWords, List.mem_append] at hx
      exact hx.elim (hf.1 x) (hi x)

/-- PIN2 analogue of `Whole431.source_success`: the actual generated entry point's
success determines all bytes and proves every serialized field word canonical.
There is no capacity/allocator premise. -/
theorem source_success (p : Public) (out : ByteVec)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p =
      ok (.Ok out)) :
    canonical ((AspisR1.PIN2_PublicBytesRefinement.steps p).flatMap stepWords) ∧
      out.val = (AspisR1.PIN2_PublicBytesRefinement.steps p).flatMap
        AspisR1.PIN2_PublicBytesRefinement.stepBytes := by
  have h' := h
  rw [AspisR1.PIN2_PublicBytesRefinement.source_eq_program] at h'
  refine ⟨program_canonical _ _ _ h', ?_⟩
  have hs := AspisR1.PIN2_PublicBytesRefinement.program_success _ _ out h'
  simpa only [alloc.vec.Vec.new, List.nil_append] using hs

#print axioms program_canonical
#print axioms source_success
end AspisR1PublicSerializer.PIN2Whole
