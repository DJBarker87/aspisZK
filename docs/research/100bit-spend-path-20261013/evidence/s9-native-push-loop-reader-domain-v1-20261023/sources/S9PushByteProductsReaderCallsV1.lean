import S9ActualDotRangeBoundsV1
import S9NativeFieldDivisionBoundV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PushByteProductsReaderCallsV1
open AspisR1S9NativeFieldS5BoundedReaderV1
open AspisR1S9NativeFieldDivisionBoundV1
open AspisR1S9OwnedFromLimbsMapV1 (mapResult)
abbrev Iter := core.ops.range.Range Usize
abbrev Dot := fast_pairing.EbyKDot
abbrev State := Iter × Dot
abbrev Output := core.result.Result Unit verifier.Error × Dot
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Every real successful body either exhausted its iterator, or read an
actual coefficient within the SAME quotient domain. Even the source's
parse-error terminal branch retains the actual field and push witnesses. -/
theorem body_success_reader_call (f : Slice U8)
    (scratch : Slice aspis_core.field.QM31) (n : Usize)
    (iter : Iter) (dot : Dot) (flow : ControlFlow State Output)
    (hdiv : (Slice.len f / 32#usize : Result Usize)=.ok n)
    (hend : iter.end.val ≤ n.val)
    (hbody : weights.push_byte_products_loop.body f scratch iter dot=.ok flow) :
    (∃ iterNext, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=
      .ok (none,iterNext)) ∨
    ∃ (j : Usize) (iterNext : Iter) (w : aspis_core.field.wide_exact.WideExact)
      (q : aspis_core.field.QM31) (r : core.result.Result Unit Unit) (dotNext : Dot),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterNext) ∧
      j.val < n.val ∧ weights.field f j=.ok w ∧
      Slice.index_usize scratch j=.ok q ∧ fast_pairing.EbyKDot.push dot w q=.ok (r,dotNext) ∧
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f j=.ok (toS5 w) := by
  unfold weights.push_byte_products_loop.body at hbody
  obtain ⟨next,hnext,hbody⟩ := bind_success _ _ _ hbody
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact Or.inl ⟨iterNext,hnext⟩
  | some j =>
    obtain ⟨w,hw,hbody⟩ := bind_success _ _ _ hbody
    obtain ⟨q,hq,hbody⟩ := bind_success _ _ _ hbody
    obtain ⟨p,hpush,hbody⟩ := bind_success _ _ _ hbody
    rcases p with ⟨r,dotNext⟩
    obtain ⟨hj,hlt,hstart,he⟩ :=
      AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter iterNext j hnext
    have hjn : j.val < n.val := by omega
    have hm := quotient_index_maps_s5_reader f n j hdiv hjn
    have hreader : AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f j=.ok (toS5 w) := by
      rw [hw] at hm
      exact hm.symm
    exact Or.inr ⟨j,iterNext,w,q,r,dotNext,hnext,hjn,hw,hq,hpush,hreader⟩

/-- Successful continuation preserves the real iterator end, so an initial
0..n loop never loses the quotient bound. -/
theorem body_cont_end (f : Slice U8) (scratch : Slice aspis_core.field.QM31)
    (iter iterNext : Iter) (dot dotNext : Dot)
    (hbody : weights.push_byte_products_loop.body f scratch iter dot=
      .ok (.cont (iterNext,dotNext))) : iterNext.end=iter.end := by
  unfold weights.push_byte_products_loop.body at hbody
  obtain ⟨next,hnext,hbody⟩ := bind_success _ _ _ hbody
  rcases next with ⟨opt,it⟩
  cases opt with
  | none => cases hbody
  | some j =>
    obtain ⟨w,hw,hbody⟩ := bind_success _ _ _ hbody
    obtain ⟨q,hq,hbody⟩ := bind_success _ _ _ hbody
    obtain ⟨p,hpush,hbody⟩ := bind_success _ _ _ hbody
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases hbody
    | Ok u =>
      cases u
      have hpair : (it,d)=(iterNext,dotNext) :=
        ControlFlow.cont.inj (Result.ok.inj hbody)
      have hit : it=iterNext := congrArg Prod.fst hpair
      have he := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter it j hnext).2.2.2
      simpa only [hit] using he

/-- A finite SAME-source execution prefix; no hypothetical child reads or
postulated field-success predicates occur in this reachability relation. -/
inductive Reached (f : Slice U8) (scratch : Slice aspis_core.field.QM31) (n : Usize)
    (initial : Dot) : State → Prop
  | initial : Reached f scratch n initial ({start:=0#usize,«end»:=n},initial)
  | next {s t : State} : Reached f scratch n initial s →
      weights.push_byte_products_loop.body f scratch s.1 s.2=.ok (.cont t) →
      Reached f scratch n initial t

theorem reached_end (f : Slice U8) (scratch : Slice aspis_core.field.QM31)
    (n : Usize) (initial : Dot) (s : State) (hr : Reached f scratch n initial s) : s.1.end=n := by
  induction hr with
  | initial => rfl
  | @next s t prior hb ih =>
    rcases s with ⟨it,d⟩; rcases t with ⟨it1,d1⟩
    exact (body_cont_end f scratch it it1 d d1 hb).trans ih

/-- At every actually reached successful source step, the field read is the
existing S5 checked reader at that SAME index and value. The done/none case
has no coefficient call. -/
theorem reached_success_reader_call (f : Slice U8)
    (scratch : Slice aspis_core.field.QM31) (n : Usize) (initial : Dot)
    (s : State) (flow : ControlFlow State Output)
    (hdiv : (Slice.len f / 32#usize : Result Usize)=.ok n)
    (hr : Reached f scratch n initial s)
    (hb : weights.push_byte_products_loop.body f scratch s.1 s.2=.ok flow) :
    (∃ iterNext, core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=
      .ok (none,iterNext)) ∨
    ∃ (j : Usize) (iterNext : Iter) (w : aspis_core.field.wide_exact.WideExact)
      (q : aspis_core.field.QM31) (r : core.result.Result Unit Unit) (dotNext : Dot),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=.ok (some j,iterNext) ∧
      j.val < n.val ∧ weights.field f j=.ok w ∧
      Slice.index_usize scratch j=.ok q ∧ fast_pairing.EbyKDot.push s.2 w q=.ok (r,dotNext) ∧
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f j=.ok (toS5 w) := by
  exact body_success_reader_call f scratch n s.1 s.2 flow hdiv
    (by rw [reached_end f scratch n initial s hr]) hb

#print axioms body_success_reader_call
#print axioms body_cont_end
#print axioms reached_end
#print axioms reached_success_reader_call
end AspisR1S9PushByteProductsReaderCallsV1
