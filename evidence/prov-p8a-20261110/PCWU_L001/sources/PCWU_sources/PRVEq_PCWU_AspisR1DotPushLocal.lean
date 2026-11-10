-- PCWU_ (P8a): fresh = gate for gate module AspisR1DotPushLocal (Types + Funs).
-- Fresh emission: PCWU_E001 (original pair: Charon XRa daad69be / Aeneas 959659a6, frozen 4bb3b3f,
-- overflow checks ON, root fast_pairing::canonical::Dot::push, Q::raw opaque).
-- The fresh text below is the E001 emission verbatim (Types.lean, Funs.lean) under namespace
-- PRVFresh_PCWU_DotPush, with two mechanical changes: the header options raising maxHeartbeats/maxRecDepth
-- are dropped (default 200000), and the one external (axiom fast_pairing.canonical.Q.raw, FunsExternal)
-- is a parameter `rawFn` of push (the Ext transformation), matching the gate's own `rawFn` parameter.
-- The equality is parametric in rawFn: CONDITIONAL_ON_BINDING (rawFn := the frozen Q::raw).
import Aeneas
import AspisR1DotPushLocal.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section

namespace PRVFresh_PCWU_DotPush

@[reducible]
def fast_pairing.canonical.Q := Array Std.U32 4#usize

structure fast_pairing.canonical.Dot where
  sums : Array Std.U64 4#usize

@[global_simps, irreducible]
def fast_pairing.canonical.P : Std.U32 := 2147483647#u32

@[rust_loop_body]
def fast_pairing.canonical.Dot.push_loop.body
  (raw1 : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (self : fast_pairing.canonical.Dot) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    fast_pairing.canonical.Dot) fast_pairing.canonical.Dot)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done self)
  | some j =>
    let i ← Array.index_usize self.sums j
    let i1 ← Array.index_usize raw1 j
    let i2 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
    let i3 ← lift (i1 &&& i2)
    let i4 ← i1 >>> 31#u32
    let i5 ← lift (core.num.U64.wrapping_add i3 i4)
    let i6 ← lift (core.num.U64.wrapping_add i i5)
    let a ← Array.update self.sums j i6
    ok (cont (iter1, { sums := a }))

@[rust_loop]
def fast_pairing.canonical.Dot.push_loop
  (iter : core.ops.range.Range Std.Usize) (self : fast_pairing.canonical.Dot)
  (raw1 : Array Std.U64 4#usize) :
  Result fast_pairing.canonical.Dot
  := do
  loop
    (fun (iter1, self1) => fast_pairing.canonical.Dot.push_loop.body raw1 iter1
      self1)
    (iter, self)

def fast_pairing.canonical.Dot.push
  (rawFn : fast_pairing.canonical.Q → fast_pairing.canonical.Q → Result (Array Std.U64 4#usize))
  (self : fast_pairing.canonical.Dot) (a : fast_pairing.canonical.Q)
  (b : fast_pairing.canonical.Q) :
  Result fast_pairing.canonical.Dot
  := do
  let raw1 ← rawFn a b
  fast_pairing.canonical.Dot.push_loop { start := 0#usize, «end» := 4#usize }
    self raw1

end PRVFresh_PCWU_DotPush

namespace PCWU_DotPushProof
open PRVFresh_PCWU_DotPush

-- one step of the fresh loop, as a plain function of the iteration index
def stepF (raw1 : Array Std.U64 4#usize) (j : Std.Usize) (self : fast_pairing.canonical.Dot) :
    Result fast_pairing.canonical.Dot := do
    let i ← Array.index_usize self.sums j
    let i1 ← Array.index_usize raw1 j
    let i2 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
    let i3 ← lift (i1 &&& i2)
    let i4 ← i1 >>> 31#u32
    let i5 ← lift (core.num.U64.wrapping_add i3 i4)
    let i6 ← lift (core.num.U64.wrapping_add i i5)
    let a ← Array.update self.sums j i6
    ok { sums := a }

theorem next_some (k k' : Std.Usize) (hlt : k.val < (4#usize).val) (hk : k'.val = k.val + 1) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := k, «end» := 4#usize }
      = ok (some k, { start := k', «end» := 4#usize }) := by
  have h := core.iter.range.IteratorRange.next_Usize_some_spec { start := k, «end» := 4#usize } hlt
  revert h
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := k, «end» := 4#usize } with
  | ok x =>
    obtain ⟨o, r'⟩ := x
    obtain ⟨s0, e0⟩ := r'
    intro h
    first | simp only [WP.spec_ok, uncurry_apply_pair] at h | simp only [WP.spec_ok] at h
    obtain ⟨ho, hs, he⟩ := h
    have hs' : s0 = k' := UScalar.eq_of_val_eq (hs.trans hk.symm)
    have ho' : o = some k := ho
    have he' : e0 = 4#usize := he
    subst ho' hs' he'
    rfl
  | fail e => intro h; first | simp [WP.spec, WP.theta] at h | simp [WP.spec] at h | exact absurd h (by simp [WP.spec, WP.theta])
  | div => intro h; first | simp [WP.spec, WP.theta] at h | simp [WP.spec] at h | exact absurd h (by simp [WP.spec, WP.theta])

theorem next_none :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := 4#usize, «end» := 4#usize }
      = ok (none, { start := 4#usize, «end» := 4#usize }) := by
  have h := core.iter.range.IteratorRange.next_Usize_none_spec { start := 4#usize, «end» := 4#usize } (Nat.le_refl _)
  revert h
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := 4#usize, «end» := 4#usize } with
  | ok x =>
    obtain ⟨o, r'⟩ := x
    intro h
    first | simp only [WP.spec_ok, uncurry_apply_pair] at h | simp only [WP.spec_ok] at h
    obtain ⟨ho, hr⟩ := h
    subst ho hr
    rfl
  | fail e => intro h; first | simp [WP.spec, WP.theta] at h | simp [WP.spec] at h | exact absurd h (by simp [WP.spec, WP.theta])
  | div => intro h; first | simp [WP.spec, WP.theta] at h | simp [WP.spec] at h | exact absurd h (by simp [WP.spec, WP.theta])

theorem loop_step (raw1 : Array Std.U64 4#usize) (k k' : Std.Usize) (hlt : k.val < (4#usize).val)
    (hk : k'.val = k.val + 1) (s : fast_pairing.canonical.Dot) :
    fast_pairing.canonical.Dot.push_loop { start := k, «end» := 4#usize } s raw1
      = (do let s' ← stepF raw1 k s; fast_pairing.canonical.Dot.push_loop { start := k', «end» := 4#usize } s' raw1) := by
  unfold fast_pairing.canonical.Dot.push_loop
  rw [loop]
  simp only [fast_pairing.canonical.Dot.push_loop.body, next_some k k' hlt hk, bind_tc_ok, stepF, bind_assoc_eq]
  generalize hm : Array.index_usize s.sums k = m
  cases m <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i
  cases Array.index_usize raw1 k <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i1
  cases lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P) <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i2
  cases lift (i1 &&& i2) <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i3
  cases i1 >>> 31#u32 <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i4
  cases lift (core.num.U64.wrapping_add i3 i4) <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i5
  cases lift (core.num.U64.wrapping_add i i5) <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]
  rename_i i6
  cases Array.update s.sums k i6 <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div]

theorem loop_done (raw1 : Array Std.U64 4#usize) (s : fast_pairing.canonical.Dot) :
    fast_pairing.canonical.Dot.push_loop { start := 4#usize, «end» := 4#usize } s raw1 = ok s := by
  unfold fast_pairing.canonical.Dot.push_loop
  rw [loop]
  simp only [fast_pairing.canonical.Dot.push_loop.body, next_none, bind_tc_ok]

theorem P_eq : PRVFresh_PCWU_DotPush.fast_pairing.canonical.P = AspisR1DotPushLocal.canonical.P := by
  unfold PRVFresh_PCWU_DotPush.fast_pairing.canonical.P AspisR1DotPushLocal.canonical.P
  rfl

theorem shr31 (x : Std.U64) : (x >>> 31#u32 : Result Std.U64) = (x >>> 31#i32 : Result Std.U64) := by
  show UScalar.shiftRight_UScalar x 31#u32 = UScalar.shiftRight_IScalar x 31#i32
  unfold UScalar.shiftRight_UScalar UScalar.shiftRight_IScalar
  have h1 : (31#u32).val = 31 := by first | rfl | decide | simp
  have h2 : (31#i32).val = 31 := by first | rfl | decide | simp
  have h3 : (31#i32).toNat = 31 := by first | rfl | decide | simp [IScalar.toNat]
  rw [h1, h2, h3]
  simp

def Dot.toGate (d : fast_pairing.canonical.Dot) : AspisR1DotPushLocal.canonical.Dot := { sums := d.sums }

end PCWU_DotPushProof

open PCWU_DotPushProof in
theorem PRVEq.AspisR1DotPushLocal.Types.canonical.Q :
    @PRVFresh_PCWU_DotPush.fast_pairing.canonical.Q = @AspisR1DotPushLocal.canonical.Q := rfl
#print axioms PRVEq.AspisR1DotPushLocal.Types.canonical.Q

def PRVEq.AspisR1DotPushLocal.Types.canonical.Dot.equiv :
    PRVFresh_PCWU_DotPush.fast_pairing.canonical.Dot ≃ AspisR1DotPushLocal.canonical.Dot where
  toFun x := { sums := x.sums }
  invFun y := { sums := y.sums }
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
#print axioms PRVEq.AspisR1DotPushLocal.Types.canonical.Dot.equiv

theorem PRVEq.AspisR1DotPushLocal.Funs.canonical.P :
    PRVFresh_PCWU_DotPush.fast_pairing.canonical.P = AspisR1DotPushLocal.canonical.P :=
  PCWU_DotPushProof.P_eq
#print axioms PRVEq.AspisR1DotPushLocal.Funs.canonical.P

open PCWU_DotPushProof in
/-- fresh = gate for Dot.push, for every rawFn (CONDITIONAL_ON_BINDING rawFn := frozen Q::raw):
    the fresh loop over 0..4 and the gate's four literal steps return the same Dot (through the equiv). -/
theorem PRVEq.AspisR1DotPushLocal.Funs.canonical.Dot.push
    (rawFn : PRVFresh_PCWU_DotPush.fast_pairing.canonical.Q → PRVFresh_PCWU_DotPush.fast_pairing.canonical.Q
      → Result (Array Std.U64 4#usize))
    (self : PRVFresh_PCWU_DotPush.fast_pairing.canonical.Dot) (a b : PRVFresh_PCWU_DotPush.fast_pairing.canonical.Q) :
    (do let d ← PRVFresh_PCWU_DotPush.fast_pairing.canonical.Dot.push rawFn self a b
        ok (PRVEq.AspisR1DotPushLocal.Types.canonical.Dot.equiv d))
      = AspisR1DotPushLocal.canonical.Dot.push rawFn
          (PRVEq.AspisR1DotPushLocal.Types.canonical.Dot.equiv self) a b := by
  unfold PRVFresh_PCWU_DotPush.fast_pairing.canonical.Dot.push AspisR1DotPushLocal.canonical.Dot.push
  have h0 : (0#usize : Std.Usize).val < (4#usize : Std.Usize).val := by first | simp | scalar_tac | decide
  have h1 : (1#usize : Std.Usize).val < (4#usize : Std.Usize).val := by first | simp | scalar_tac | decide
  have h2 : (2#usize : Std.Usize).val < (4#usize : Std.Usize).val := by first | simp | scalar_tac | decide
  have h3 : (3#usize : Std.Usize).val < (4#usize : Std.Usize).val := by first | simp | scalar_tac | decide
  have e1 : (1#usize : Std.Usize).val = (0#usize : Std.Usize).val + 1 := by first | simp | scalar_tac | decide
  have e2 : (2#usize : Std.Usize).val = (1#usize : Std.Usize).val + 1 := by first | simp | scalar_tac | decide
  have e3 : (3#usize : Std.Usize).val = (2#usize : Std.Usize).val + 1 := by first | simp | scalar_tac | decide
  have e4 : (4#usize : Std.Usize).val = (3#usize : Std.Usize).val + 1 := by first | simp | scalar_tac | decide
  cases rawFn a b with
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok raw1 =>
    simp only [bind_tc_ok]
    simp only [loop_step raw1 0#usize 1#usize h0 e1, loop_step raw1 1#usize 2#usize h1 e2,
      loop_step raw1 2#usize 3#usize h2 e3, loop_step raw1 3#usize 4#usize h3 e4, loop_done,
      stepF, bind_assoc_eq, bind_tc_ok, P_eq, shr31]
    rfl
#print axioms PRVEq.AspisR1DotPushLocal.Funs.canonical.Dot.push
