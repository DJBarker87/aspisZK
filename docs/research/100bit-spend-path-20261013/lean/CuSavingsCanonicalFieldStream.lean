import CuSavingsCanonicalFieldStreamLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalFieldStream
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalFieldStreamLoop
open CuSavingsCanonicalDotsField (WideCanonical)
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
    have hc := field_canonical f j input hinput
    have he := Result.ok.inj h
    cases he
    exact hc

theorem old_body_factor (f : Slice U8) (scratch : Slice K) (iter : Range)
    (pair : old_pairing.EbyKDot) :
    old_stream.field_stream_loop.body f scratch iter pair =
      body (fetch f scratch) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish (iter,pair) := by
  unfold old_stream.field_stream_loop.body body fetch
  simp only [bind_assoc_eq]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      simp only [uncurry_apply_pair,bind_assoc_eq,bind_tc_ok]
      apply (bind_eq_iff (weights.field f index) _ _).mpr
      intro value _
      apply (bind_eq_iff (Slice.index_usize scratch index) _ _).mpr
      intro scalar _
      apply (bind_eq_iff (old_pairing.EbyKDot.push pair value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        old_stream.field_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        old_stream.field_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem new_body_factor (f : Slice U8) (scratch : Slice K) (iter : Range)
    (pair : new_pairing.EbyKDot) :
    new_stream.field_stream_loop.body f scratch iter pair =
      body (fetch f scratch) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish (iter,pair) := by
  unfold new_stream.field_stream_loop.body body fetch
  simp only [bind_assoc_eq]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      simp only [uncurry_apply_pair,bind_assoc_eq,bind_tc_ok]
      apply (bind_eq_iff (weights.field f index) _ _).mpr
      intro value _
      apply (bind_eq_iff (Slice.index_usize scratch index) _ _).mpr
      intro scalar _
      apply (bind_eq_iff (new_pairing.EbyKDot.push pair value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        new_stream.field_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        new_stream.field_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

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
