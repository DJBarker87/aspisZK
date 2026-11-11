import JFs_SerializerFragment
import PIN2_PublicSerializerWhole

/-! PIN2 W6 (2026-11-11): PIN2 counterpart of `JFs_SerializerProgram.source`.
A run of W3b's PIN2 instruction program (`PIN2_PublicBytesRefinement.program`,
which IS the generated PIN2 `public_bytes` by `source_eq_program`) succeeds and
writes exactly `ss.flatMap stepBytes`, given canonical field words and vector
capacity (the same two premises as the release lemma).  Word and frontier
steps reuse the frozen helper successes through W3b's transport equations
`fields_eq`/`frontier_eq`; byte/index/raw steps are the shared std pushes.
New module; no release counterpart. -/
set_option autoImplicit false
namespace AspisR1.PIN2W6_SerializerProgram
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1.PIN2_PublicBytesRefinement (Step program stepBytes nextPublic)
open AspisR1.PIN2_SerializerTransport (NewError mapPairOutcome mapStatus)

abbrev stepWords := AspisR1PublicSerializer.PIN2Whole.stepWords

theorem new_of_mapped (m : Result (core.result.Result Unit NewError × ByteVec)) (u : ByteVec)
    (h : mapPairOutcome m = ok (.Ok (), u)) : m = ok (.Ok (), u) := by
  cases m with
  | ok p =>
    rcases p with ⟨s, out⟩
    cases s with
    | Ok x => cases x; simp only [mapPairOutcome, mapStatus] at h; cases h; rfl
    | Err e => simp only [mapPairOutcome, mapStatus] at h; cases h
  | fail e => simp only [mapPairOutcome] at h; cases h
  | div => simp only [mapPairOutcome] at h; cases h

theorem next_ok (u : ByteVec) (k : ByteVec → Result PIN2_PublicBytesRefinement.Output) :
    nextPublic (ok (.Ok (), u)) k = k u := rfl

theorem step (s : Step) (ss : List Step) (out : ByteVec) (canon : canonical (stepWords s))
    (cap : out.length + (stepBytes s).length ≤ Usize.max) :
    ∃ u, u.val = out.val ++ stepBytes s ∧ program (s :: ss) out = program ss u := by
  cases s with
  | byte b =>
    have room : out.val.length < Usize.max := by
      simp only [stepBytes, List.length_cons, List.length_nil] at cap
      change out.val.length + 1 ≤ Usize.max at cap
      omega
    obtain ⟨u, call, bytes⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out b room)
    exact ⟨u, by simpa only [stepBytes] using bytes, by simp only [program, call, bind_tc_ok]⟩
  | words v =>
    have room : out.length + 4 * v.length ≤ Usize.max := by
      simpa only [stepBytes, JFs_SerializerLengths.words] using cap
    obtain ⟨u, old, bytes⟩ := fields_canonical_append out v canon room
    rw [PIN2_SerializerTransport.fields_eq] at old
    have new := new_of_mapped _ u old
    exact ⟨u, bytes, by simp only [program, new, next_ok]⟩
  | frontier f =>
    have room : out.length + 4 * ((AspisR1PublicSerializer.Frontier431.rows f).flatMap
        (fun s => s.val)).length ≤ Usize.max := by
      simpa only [stepBytes, JFs_SerializerLengths.words] using cap
    obtain ⟨u, call, bytes⟩ := JFs_SerializerChain.source
      (AspisR1PublicSerializer.Frontier431.rows f) out canon room
    have old := (AspisR1PublicSerializer.Frontier431.frontier_eq_chain out f).trans call
    rw [PIN2_SerializerTransport.frontier_eq] at old
    have new := new_of_mapped _ u old
    exact ⟨u, bytes, by simp only [program, new, next_ok]⟩
  | index n =>
    have room : out.length + (Array.to_slice (core.num.U64.to_le_bytes n)).length ≤ Usize.max := cap
    obtain ⟨u, call, bytes⟩ := extend_u8 out (Array.to_slice (core.num.U64.to_le_bytes n)) room
    exact ⟨u, bytes, by simp only [program, call, bind_tc_ok]⟩
  | raw a =>
    have room : out.length + (Array.to_slice a).length ≤ Usize.max := cap
    obtain ⟨u, call, bytes⟩ := extend_u8 out (Array.to_slice a) room
    exact ⟨u, bytes, by simp only [program, call, bind_tc_ok]⟩

theorem source (ss : List Step) (out : ByteVec)
    (canon : canonical (ss.flatMap stepWords))
    (cap : out.length + (ss.flatMap stepBytes).length ≤ Usize.max) :
    ∃ updated, program ss out = ok (.Ok updated) ∧ updated.val = out.val ++ ss.flatMap stepBytes := by
  induction ss generalizing out with
  | nil => exact ⟨out, rfl, by simp⟩
  | cons s ss ih =>
    have hc : canonical (stepWords s) := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl hx)
    have hs : canonical (ss.flatMap stepWords) := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hx)
    have capFirst : out.length + (stepBytes s).length ≤ Usize.max := by
      simp only [List.flatMap_cons, List.length_append] at cap
      omega
    obtain ⟨middle, bytes, call⟩ := step s ss out hc capFirst
    have middleLength : middle.length = out.length + (stepBytes s).length := by
      change middle.val.length = out.val.length + (stepBytes s).length
      rw [bytes, List.length_append]
    have capRest : middle.length + (ss.flatMap stepBytes).length ≤ Usize.max := by
      rw [middleLength]
      simp only [List.flatMap_cons, List.length_append] at cap
      omega
    obtain ⟨updated, tail, contents⟩ := ih middle hs capRest
    refine ⟨updated, call.trans tail, ?_⟩
    simpa only [List.flatMap_cons, bytes, List.append_assoc] using contents

/-- The generated PIN2 entry point succeeds on any carrier whose serialized field
words are canonical and whose image fits (premises as in the release). -/
theorem public_bytes (q : PIN2_PublicBytesRefinement.NewPublic)
    (canon : canonical ((PIN2_PublicBytesRefinement.steps q).flatMap stepWords))
    (cap : ((PIN2_PublicBytesRefinement.steps q).flatMap stepBytes).length ≤ Usize.max) :
    ∃ encoded, AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok encoded) ∧ encoded.val = (PIN2_PublicBytesRefinement.steps q).flatMap stepBytes := by
  have cap' : (alloc.vec.Vec.new U8).length + ((PIN2_PublicBytesRefinement.steps q).flatMap stepBytes).length ≤ Usize.max := by
    change 0 + _ ≤ Usize.max; omega
  obtain ⟨encoded, call, bytes⟩ := source _ (alloc.vec.Vec.new U8) canon cap'
  refine ⟨encoded, (PIN2_PublicBytesRefinement.source_eq_program q).trans call, ?_⟩
  simpa only [alloc.vec.Vec.new, List.nil_append] using bytes

#print axioms new_of_mapped
#print axioms step
#print axioms source
#print axioms public_bytes
end AspisR1.PIN2W6_SerializerProgram
