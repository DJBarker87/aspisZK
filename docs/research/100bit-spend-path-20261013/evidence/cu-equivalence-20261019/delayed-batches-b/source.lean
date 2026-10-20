import CuSavingsDelayedLimbLoop
import CuSavingsDelayedCommon
import CuSavingsDelayedIterator
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedBatches
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1DelayedDots AspisV8R17.RawReducer
open CuSavingsDelayedArrays CuSavingsDelayedScalar CuSavingsResidues
open CuSavingsDelayedIterator
variable [Shared]

def dispatch {A B : Type} (k : A → Result B) (r : Result (ControlFlow A B)) : Result B := do
  let flow ← r
  match flow with | .cont a => k a | .done b => .ok b

private theorem dispatch_bind {A B X : Type} (k : A → Result B) (r : Result X)
    (f : X → Result (ControlFlow A B)) :
    dispatch k (r >>= f) = (do let x ← r;dispatch k (f x)) := by
  cases r <;> rfl

theorem old_unroll (iter : Iter) (bytes : Slice U8)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize) (limbs : Canon) :
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 iter bytes gamma slot limbs = (do
      let (opt,next) ← core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
      match opt with
      | none => .ok limbs
      | some start =>
        let stop0 ← start + 4#usize
        let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
        let sums ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0 {start,«end» := stop}
          bytes gamma slot (Array.repeat 8#usize 0#u64)
        let out ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
          {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} limbs sums
        old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 next bytes gamma slot out) := by
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
  rw [loop]
  change dispatch (fun (it,l) => old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 it bytes gamma slot l)
    (old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body bytes gamma slot iter limbs) = _
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
  rw [dispatch_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro pair hp
  rcases pair with ⟨opt,next⟩
  cases opt with
  | none => rfl
  | some start =>
    change dispatch _ (do
      let stop0 ← start + 4#usize
      let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
      let sums ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0 {start,«end» := stop}
        bytes gamma slot (Array.repeat 8#usize 0#u64)
      let out ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} limbs sums
      .ok (.cont (next,out))) = _
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro stop0 h0
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro stop h1
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro sums h2
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro out h3
    rfl

theorem new_unroll (iter : Iter) (bytes : Slice U8)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize) (limbs : Raw) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 iter bytes gamma slot limbs = (do
      let (opt,next) ← core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
      match opt with
      | none => .ok limbs
      | some start =>
        let stop0 ← start + 4#usize
        let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
        let sums ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0 {start,«end» := stop}
          bytes gamma slot (Array.repeat 8#usize 0#u64)
        let out ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
          {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} limbs sums
        new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 next bytes gamma slot out) := by
  unfold new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
  rw [loop]
  change dispatch (fun (it,l) => new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 it bytes gamma slot l)
    (new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body bytes gamma slot iter limbs) = _
  unfold new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
  rw [dispatch_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro pair hp
  rcases pair with ⟨opt,next⟩
  cases opt with
  | none => rfl
  | some start =>
    change dispatch _ (do
      let stop0 ← start + 4#usize
      let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
      let sums ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0 {start,«end» := stop}
        bytes gamma slot (Array.repeat 8#usize 0#u64)
      let out ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} limbs sums
      .ok (.cont (next,out))) = _
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro stop0 h0
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro stop h1
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro sums h2
    rw [dispatch_bind]
    apply (bind_eq_iff _ _ _).mpr
    intro out h3
    rfl

def Residues (old : Canon) (raw : Raw) : Prop :=
  ∀ j : Fin 8, (wordAt old j).val = (wordAt raw j).val%P

theorem next_state (count : Nat) (o : Canon) (r : Raw) (h : State count 8 o r) :
    State (count+1) 0 o r := by
  intro j
  have hj := h j
  simpa only [j.isLt,Nat.not_lt_zero,↓reduceIte,Nat.add_assoc] using hj


theorem source_transport {A : Type} (fuel count : Nat) (iter : Iter)
    (bytes : Slice U8) (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (old : Canon) (raw : Raw) (hc : count ≤ 7) (hf : 7-count = fuel)
    (hi : At count iter) (h : State count 0 old raw)
    (kRaw : Raw → Result A) (kOld : Canon → Result A)
    (hk : ∀ o r, Residues o r → kRaw r = kOld o) :
    (do let r ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
          iter bytes gamma slot raw
        kRaw r) =
    (do let o ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
          iter bytes gamma slot old
        kOld o) := by
  induction fuel generalizing count iter old raw with
  | zero =>
    have hc7 : count = 7 := by omega
    subst count
    obtain ⟨next,hn⟩ := CuSavingsDelayedIterator.next_done iter hi
    rw [old_unroll,new_unroll]
    simp only [hn,bind_tc_ok]
    change kRaw raw = kOld old
    exact hk old raw (fun j => (h j).1)
  | succ fuel ih =>
    have hc7 : count < 7 := by omega
    obtain ⟨next,hn,hnAt⟩ := CuSavingsDelayedIterator.next_step count iter hi hc7
    rw [old_unroll,new_unroll]
    simp only [hn,bind_tc_ok]
    dsimp only
    simp only [bind_assoc_eq]
    change (do
      let stop0 ← iter.iter.start + 4#usize
      let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
      let sums ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        {start := iter.iter.start,«end» := stop} bytes gamma slot (Array.repeat 8#usize 0#u64)
      let out ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} raw sums
      let r ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        next bytes gamma slot out
      kRaw r) = (do
      let stop0 ← iter.iter.start + 4#usize
      let stop ← core.cmp.min core.cmp.OrdUsize stop0 26#usize
      let sums ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        {start := iter.iter.start,«end» := stop} bytes gamma slot (Array.repeat 8#usize 0#u64)
      let out ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} old sums
      let o ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        next bytes gamma slot out
      kOld o)
    apply (bind_eq_iff _ _ _).mpr
    intro stop0 h0
    apply (bind_eq_iff _ _ _).mpr
    intro stop h1
    rw [CuSavingsDelayedCommon.base_eq]
    apply (bind_eq_iff _ _ _).mpr
    intro sums h2
    obtain ⟨o,r,ho,hr,hstate⟩ := CuSavingsDelayedLimbLoop.source_both 8
      {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT}
      sums old raw count hc7 (by simp [field.wide_exact.WideExact.LIMB_COUNT])
      (by scalar_tac) (by scalar_tac) (by simpa only [show (0#usize).val=0 by scalar_tac] using h)
    rw [ho,hr,bind_tc_ok,bind_tc_ok]
    exact ih (count+1) next o r (by omega) (by omega) hnAt (next_state count o r hstate)

#print axioms old_unroll
#print axioms new_unroll
#print axioms next_state
#print axioms source_transport
end AspisR1.CuSavingsDelayedBatches
