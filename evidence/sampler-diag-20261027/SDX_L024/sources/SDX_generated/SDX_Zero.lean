import SDX_Common
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDX_Zero
open SDX_Common
def st0 : Iter := mk [] (by scalar_tac)
def st1 : Iter := mk [0#u32] (by scalar_tac)
def st2 : Iter := mk [0#u32,0#u32] (by scalar_tac)
def st3 : Iter := mk [0#u32,0#u32,0#u32] (by scalar_tac)
def st4 : Iter := mk [0#u32,0#u32,0#u32,0#u32] (by scalar_tac)
def st5 : Iter := mk [0#u32,0#u32,0#u32,0#u32,0#u32] (by scalar_tac)
def st6 : Iter := mk [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32] (by scalar_tac)
def st7 : Iter := mk [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32] (by scalar_tac)
def st8 : Iter := mk [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32] (by scalar_tac)
def fin0 (b : Back) : Back := b
def fin1 (b : Back) : Back := fin0 (fun r => b (restore st1 0#u32 r))
def fin2 (b : Back) : Back := fin1 (fun r => b (restore st2 0#u32 r))
def fin3 (b : Back) : Back := fin2 (fun r => b (restore st3 0#u32 r))
def fin4 (b : Back) : Back := fin3 (fun r => b (restore st4 0#u32 r))
def fin5 (b : Back) : Back := fin4 (fun r => b (restore st5 0#u32 r))
def fin6 (b : Back) : Back := fin5 (fun r => b (restore st6 0#u32 r))
def fin7 (b : Back) : Back := fin6 (fun r => b (restore st7 0#u32 r))
def fin8 (b : Back) : Back := fin7 (fun r => b (restore st8 0#u32 r))

theorem step1 (b : Back) : body st1 b 0#u64 =
    ok (.cont (st0, fun r => b (restore st1 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st1,st0,mk,restore]
  rfl
#print axioms step1

theorem step2 (b : Back) : body st2 b 0#u64 =
    ok (.cont (st1, fun r => b (restore st2 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st2,st1,mk,restore]
  rfl
#print axioms step2

theorem step3 (b : Back) : body st3 b 0#u64 =
    ok (.cont (st2, fun r => b (restore st3 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st3,st2,mk,restore]
  rfl
#print axioms step3

theorem step4 (b : Back) : body st4 b 0#u64 =
    ok (.cont (st3, fun r => b (restore st4 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st4,st3,mk,restore]
  rfl
#print axioms step4

theorem step5 (b : Back) : body st5 b 0#u64 =
    ok (.cont (st4, fun r => b (restore st5 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st5,st4,mk,restore]
  rfl
#print axioms step5

theorem step6 (b : Back) : body st6 b 0#u64 =
    ok (.cont (st5, fun r => b (restore st6 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st6,st5,mk,restore]
  rfl
#print axioms step6

theorem step7 (b : Back) : body st7 b 0#u64 =
    ok (.cont (st6, fun r => b (restore st7 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st7,st6,mk,restore]
  rfl
#print axioms step7

theorem step8 (b : Back) : body st8 b 0#u64 =
    ok (.cont (st7, fun r => b (restore st8 0#u32 r), 0#u64)) := by
  unfold body SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    st8,st7,mk,restore]
  rfl
#print axioms step8

theorem loop0 (b : Back) : loop step (st0,b,0#u64) = ok (0#u64,fin0 b) := by
  rw [loop.eq_def]
  change (match body st0 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  unfold st0
  rw [empty]
  rfl
#print axioms loop0

theorem loop1 (b : Back) : loop step (st1,b,0#u64) = ok (0#u64,fin1 b) := by
  rw [loop.eq_def]
  change (match body st1 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step1]
  exact loop0 _
#print axioms loop1

theorem loop2 (b : Back) : loop step (st2,b,0#u64) = ok (0#u64,fin2 b) := by
  rw [loop.eq_def]
  change (match body st2 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step2]
  exact loop1 _
#print axioms loop2

theorem loop3 (b : Back) : loop step (st3,b,0#u64) = ok (0#u64,fin3 b) := by
  rw [loop.eq_def]
  change (match body st3 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step3]
  exact loop2 _
#print axioms loop3

theorem loop4 (b : Back) : loop step (st4,b,0#u64) = ok (0#u64,fin4 b) := by
  rw [loop.eq_def]
  change (match body st4 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step4]
  exact loop3 _
#print axioms loop4

theorem loop5 (b : Back) : loop step (st5,b,0#u64) = ok (0#u64,fin5 b) := by
  rw [loop.eq_def]
  change (match body st5 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step5]
  exact loop4 _
#print axioms loop5

theorem loop6 (b : Back) : loop step (st6,b,0#u64) = ok (0#u64,fin6 b) := by
  rw [loop.eq_def]
  change (match body st6 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step6]
  exact loop5 _
#print axioms loop6

theorem loop7 (b : Back) : loop step (st7,b,0#u64) = ok (0#u64,fin7 b) := by
  rw [loop.eq_def]
  change (match body st7 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step7]
  exact loop6 _
#print axioms loop7

theorem loop8 (b : Back) : loop step (st8,b,0#u64) = ok (0#u64,fin8 b) := by
  rw [loop.eq_def]
  change (match body st8 b 0#u64 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step8]
  exact loop7 _
#print axioms loop8
end SDX_Zero
