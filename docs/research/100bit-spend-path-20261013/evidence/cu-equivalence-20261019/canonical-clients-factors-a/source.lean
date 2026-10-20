import AspisR1CanonicalDotClients.Funs
import AspisR1CanonicalDotPartials.Funs
import CuSavingsCanonicalFieldStreamLoop
import CuSavingsCanonicalDotClientInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotClientFactors
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalFieldStreamLoop
variable [Shared]
abbrev Range := core.ops.range.Range Usize
abbrev Enum := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter K)
def highNext (partials : Array E 4#usize) (scalars : Array K 4#usize) (iter : Range) : Result (Option (E×K)×Range) := do
  let (entry,after) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match entry with
  | none => .ok (none,after)
  | some s => do
    let value ← Array.index_usize partials s
    let scalar ← Array.index_usize scalars s
    .ok (some (value,scalar),after)
def rowNext (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range) : Result (Option (E×K)×Range) := do
  let (entry,after) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match entry with
  | none => .ok (none,after)
  | some j => do
    let i ← 16#usize * s
    let i1 ← i+j
    let value ← weights.field f i1
    let scalar ← Array.index_usize common j
    .ok (some (value,scalar),after)
def finalNext (f : Slice U8) (iter : Enum) : Result (Option (E×K)×Enum) := do
  let (entry,after) ← core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter K) iter
  match entry with
  | none => .ok (none,after)
  | some (j,scalar) => do
    let value ← weights.field f j
    .ok (some (value,scalar),after)

theorem old_shared_high_factor (partials : Array E 4#usize) (scalars : Array K 4#usize) (iter : Range) (dot : old_pairing.EbyKDot) :
    old_clients.shared_high_loop.body partials scalars iter dot=
      body (highNext partials scalars) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish (iter,dot) := by
  unfold old_clients.shared_high_loop.body body highNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      apply (bind_eq_iff (Array.index_usize partials index) _ _).mpr
      intro value _
      apply (bind_eq_iff (Array.index_usize scalars index) _ _).mpr
      intro scalar _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (old_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        old_clients.shared_high.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        old_clients.shared_high.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms old_shared_high_factor

theorem new_shared_high_factor (partials : Array E 4#usize) (scalars : Array K 4#usize) (iter : Range) (dot : new_pairing.EbyKDot) :
    new_clients.shared_high_loop.body partials scalars iter dot=
      body (highNext partials scalars) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish (iter,dot) := by
  unfold new_clients.shared_high_loop.body body highNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      apply (bind_eq_iff (Array.index_usize partials index) _ _).mpr
      intro value _
      apply (bind_eq_iff (Array.index_usize scalars index) _ _).mpr
      intro scalar _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (new_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        new_clients.shared_high.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        new_clients.shared_high.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms new_shared_high_factor

theorem old_shared_row_factor (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range) (dot : old_pairing.EbyKDot) :
    old_clients.shared_row_loop.body f common s iter dot=
      body (rowNext f common s) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish (iter,dot) := by
  unfold old_clients.shared_row_loop.body body rowNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      apply (bind_eq_iff (16#usize * s) _ _).mpr
      intro offset _
      apply (bind_eq_iff (offset + index) _ _).mpr
      intro position _
      apply (bind_eq_iff (weights.field f position) _ _).mpr
      intro value _
      apply (bind_eq_iff (Array.index_usize common index) _ _).mpr
      intro scalar _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (old_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        old_clients.shared_row.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        old_clients.shared_row.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms old_shared_row_factor

theorem new_shared_row_factor (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range) (dot : new_pairing.EbyKDot) :
    new_clients.shared_row_loop.body f common s iter dot=
      body (rowNext f common s) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish (iter,dot) := by
  unfold new_clients.shared_row_loop.body body rowNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      apply (bind_eq_iff (16#usize * s) _ _).mpr
      intro offset _
      apply (bind_eq_iff (offset + index) _ _).mpr
      intro position _
      apply (bind_eq_iff (weights.field f position) _ _).mpr
      intro value _
      apply (bind_eq_iff (Array.index_usize common index) _ _).mpr
      intro scalar _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (new_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        new_clients.shared_row.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        new_clients.shared_row.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms new_shared_row_factor

theorem old_final_stream_factor (f : Slice U8) (iter : Enum) (dot : old_pairing.EbyKDot) :
    old_clients.final_stream_loop.body f iter dot=
      body (finalNext f) old_pairing.EbyKDot.push old_pairing.EbyKDot.finish (iter,dot) := by
  unfold old_clients.final_stream_loop.body body finalNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter K) iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      rcases index with ⟨index,scalar⟩
      apply (bind_eq_iff (weights.field f index) _ _).mpr
      intro value _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (old_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        old_clients.final_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        old_clients.final_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms old_final_stream_factor

theorem new_final_stream_factor (f : Slice U8) (iter : Enum) (dot : new_pairing.EbyKDot) :
    new_clients.final_stream_loop.body f iter dot=
      body (finalNext f) new_pairing.EbyKDot.push new_pairing.EbyKDot.finish (iter,dot) := by
  unfold new_clients.final_stream_loop.body body finalNext
  simp only [bind_assoc_eq,uncurry_apply_pair]
  apply (bind_eq_iff (core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter K) iter) _ _).mpr
  intro fetched _
  rcases fetched with ⟨entry,after⟩
  cases entry with
  | none => rfl
  | some index =>
      rcases index with ⟨index,scalar⟩
      apply (bind_eq_iff (weights.field f index) _ _).mpr
      intro value _
      simp only [bind_tc_ok,uncurry_apply_pair]
      apply (bind_eq_iff (new_pairing.EbyKDot.push dot value scalar) _ _).mpr
      intro pushed _
      rcases pushed with ⟨result,state⟩
      cases result <;> simp [core.result.Result.map_err,
        new_clients.final_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        new_clients.final_stream.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms new_final_stream_factor

private theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

theorem rowNext_canonical (f : Slice U8) (common : Array K 16#usize) (s : Usize)
    (iter : Range) (value : E) (scalar : K) (after : Range)
    (h : rowNext f common s iter=.ok (some (value,scalar),after)) :
    CuSavingsCanonicalDotsField.WideCanonical value := by
  unfold rowNext at h
  obtain ⟨entry,_,h⟩ := bind_ok _ _ _ h
  rcases entry with ⟨entry,next⟩
  cases entry with
  | none => cases h
  | some index =>
    obtain ⟨offset,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨position,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨decoded,hd,h⟩ := bind_ok _ _ _ h
    obtain ⟨multiplier,_,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact CuSavingsCanonicalDotClientInputs.field_success f position decoded hd

theorem finalNext_canonical (f : Slice U8)
    (iter : Enum) (value : E) (scalar : K) (after : Enum)
    (h : finalNext f iter=.ok (some (value,scalar),after)) :
    CuSavingsCanonicalDotsField.WideCanonical value := by
  unfold finalNext at h
  obtain ⟨entry,_,h⟩ := bind_ok _ _ _ h
  rcases entry with ⟨entry,next⟩
  cases entry with
  | none => cases h
  | some index =>
    rcases index with ⟨index,multiplier⟩
    obtain ⟨decoded,hd,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact CuSavingsCanonicalDotClientInputs.field_success f index decoded hd

def CanonicalArray (partials : Array E 4#usize) : Prop :=
  ∀ index value,Array.index_usize partials index=.ok value →
    CuSavingsCanonicalDotsField.WideCanonical value

theorem highNext_canonical (partials : Array E 4#usize) (scalars : Array K 4#usize)
    (hc : CanonicalArray partials)
    (iter : Range) (value : E) (scalar : K) (after : Range)
    (h : highNext partials scalars iter=.ok (some (value,scalar),after)) :
    CuSavingsCanonicalDotsField.WideCanonical value := by
  unfold highNext at h
  obtain ⟨entry,_,h⟩ := bind_ok _ _ _ h
  rcases entry with ⟨entry,next⟩
  cases entry with
  | none => cases h
  | some index =>
    obtain ⟨decoded,hd,h⟩ := bind_ok _ _ _ h
    obtain ⟨multiplier,_,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact hc index decoded hd
#print axioms rowNext_canonical
#print axioms finalNext_canonical
#print axioms highNext_canonical
end AspisR1.CuSavingsCanonicalDotClientFactors
