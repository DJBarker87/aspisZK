import CuSavingsCanonicalFieldStreamLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalFieldStream
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField CuSavingsCanonicalFieldStreamLoop
variable [Shared]
abbrev Range := core.ops.range.Range Usize

def fetch (f : Slice U8) (scratch : Slice K) (iter : Range) : Result (Option (E × K) × Range) := do
  let (entry,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match entry with
  | none => .ok (none,iter1)
  | some j => do
    let value ← weights.field f j
    let scalar ← Slice.index_usize scratch j
    .ok (some (value,scalar),iter1)

private theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

theorem field_canonical (f : Slice U8) (j : Usize) (value : E)
    (h : weights.field f j=.ok value) : WideCanonical value := by
  unfold weights.field at h
  obtain ⟨input,hinput,h⟩ := bind_ok _ _ _ h
  have he := Result.ok.inj h
  cases he
  exact CuSavingsCanonicalDotsSources.input_canonical input
    (CuSavingsCanonicalInputParser.field_success f j input hinput)

theorem fetch_canonical (f : Slice U8) (scratch : Slice K)
    (iter : Range) (value : E) (scalar : K) (iter1 : Range)
    (h : fetch f scratch iter=.ok (some (value,scalar),iter1)) : WideCanonical value := by
  unfold fetch at h
  obtain ⟨entry,_,h⟩ := bind_ok _ _ _ h
  rcases entry with ⟨entry,next⟩
  cases entry with
  | none => cases h
  | some j =>
    obtain ⟨input,hinput,h⟩ := bind_ok _ _ _ h
    obtain ⟨word,_,h⟩ := bind_ok _ _ _ h
    have he := Result.ok.inj h
    cases he
    exact field_canonical f j input hinput

theorem old_body_factor (f : Slice U8) (scratch : Slice K) (iter : Range)
    (pair : old_pairing.EbyKDot) :
    old_stream.field_stream_loop.body f scratch iter pair =
      body (fetch f scratch) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish (iter,pair) := by
  unfold old_stream.field_stream_loop.body body fetch
  dsimp only
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => rfl
  | div => rfl
  | ok entry =>
    rcases entry with ⟨entry,iter1⟩
    cases entry with
    | none =>
      cases old_pairing.EbyKDot.finish pair <;> rfl
    | some j =>
      simp only [bind_tc_ok]
      dsimp only
      cases hv : weights.field f j with
      | fail e => rfl
      | div => rfl
      | ok value =>
        cases hs : Slice.index_usize scratch j with
        | fail e => rfl
        | div => rfl
        | ok scalar =>
          simp only [bind_tc_ok]
          cases hp : old_pairing.EbyKDot.push pair value scalar with
          | fail e => rfl
          | div => rfl
          | ok entry =>
            rcases entry with ⟨result,pair1⟩
            cases result <;> rfl

theorem new_body_factor (f : Slice U8) (scratch : Slice K) (iter : Range)
    (pair : new_pairing.EbyKDot) :
    new_stream.field_stream_loop.body f scratch iter pair =
      body (fetch f scratch) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish (iter,pair) := by
  unfold new_stream.field_stream_loop.body body fetch
  dsimp only
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => rfl
  | div => rfl
  | ok entry =>
    rcases entry with ⟨entry,iter1⟩
    cases entry with
    | none =>
      cases new_pairing.EbyKDot.finish pair <;> rfl
    | some j =>
      simp only [bind_tc_ok]
      dsimp only
      cases hv : weights.field f j with
      | fail e => rfl
      | div => rfl
      | ok value =>
        cases hs : Slice.index_usize scratch j with
        | fail e => rfl
        | div => rfl
        | ok scalar =>
          simp only [bind_tc_ok]
          cases hp : new_pairing.EbyKDot.push pair value scalar with
          | fail e => rfl
          | div => rfl
          | ok entry =>
            rcases entry with ⟨result,pair1⟩
            cases result <;> rfl

theorem source_loop_equivalence (f : Slice U8) (scratch : Slice K) (iter : Range)
    (pair : old_pairing.EbyKDot) (hc : RelatedCounts pair) :
    new_stream.field_stream_loop iter f scratch (project pair)=
      old_stream.field_stream_loop iter f scratch pair := by
  have ho : (fun (s : Range × old_pairing.EbyKDot) => old_stream.field_stream_loop.body f scratch s.1 s.2)=
      body (fetch f scratch) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish := by
    funext s
    exact old_body_factor f scratch s.1 s.2
  have hn : (fun (s : Range × new_pairing.EbyKDot) => new_stream.field_stream_loop.body f scratch s.1 s.2)=
      body (fetch f scratch) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish := by
    funext s
    exact new_body_factor f scratch s.1 s.2
  unfold new_stream.field_stream_loop old_stream.field_stream_loop
  rw [ho,hn]
  exact run_equivalence (fetch f scratch) (fetch_canonical f scratch) iter pair hc

theorem source_equivalence (f : Slice U8) (scratch : Slice K) (n : Usize) :
    new_stream.field_stream f scratch n=old_stream.field_stream f scratch n := by
  unfold new_stream.field_stream old_stream.field_stream
  rw [CuSavingsCanonicalDotsInvariant.new_new,CuSavingsCanonicalDotsInvariant.old_new]
  simp only [bind_tc_ok]
  exact source_loop_equivalence f scratch _ _ CuSavingsCanonicalDotsInvariant.initial_counts

#print axioms field_canonical
#print axioms fetch_canonical
#print axioms old_body_factor
#print axioms new_body_factor
#print axioms source_loop_equivalence
#print axioms source_equivalence
end AspisR1.CuSavingsCanonicalFieldStream
