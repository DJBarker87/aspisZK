import RPt_JFs_TX2_OuterStep
import RPt_JFs_TX2_BatchWindow
import RPt_JFr_TX2_DotLanes
import RPt_JFr_TX2_ScalarCanon
import RPt_FIo_RangeNext
import NEV_DotInputs
import NFS_PacketRoot
import NFW_PowersDomain

/-! NPH_ (R22, item 1 of the 2026-11-10 continuation: the op20 dots family). Lemmas about the
existing gate definitions FIp_NativeDots.fast_dots.four_dots_one, its outer StepBy loop body
four_dots_one_loop0.body and its inner term loop body four_dots_one_loop0_loop0.body; nothing
merged changes.

The cadence invariants are def predicates on the loop states:
- `InnerInv base (iter, sums)`: the term window [base, iter.end) has iter.end ≤ 26 and at most 4
  terms (iter.end ≤ base + 4), base ≤ iter.start, and every one of the 8 u64 sums is at most
  (iter.start − base)·(P−1)² (JFs_TX2_ArrayEight.Bound).
- `OuterInv (iter, limbs)`: after k ≤ 7 windows the StepBy iterator is at min(4k, 26) on the
  range end 26 with step 4, and every limb is at most k·R (JFs_TX2_FoldEight.Bound,
  R = 10737418238).
Caller domain: slot < 4 and canonical coefficients g (NEV_DotInputs.Canonical). The only
executing caller of four_dots_one is four_dots, which passes the literals 0..3 and the g it
receives; four_dots is reached only through FIp_DotsAdapter.dots (op20 of the installed query
dictionaries) on toArray g (backward screen NPH_REFS5.json, textual, flagged). There g is
canonical: NFS_PacketRoot.Domain.gCanonical on tx1 (`tx1_g`), NFW_PowersDomain.query_domain on
tx2.

Proved:
- `slot_ops`: every checked operation of four_dots_one's own body (slot*120, +104, +120,
  slot*32, 480+·, 0*16, 1*16, +26, +16) is ok for slot < 4.
- `read_arith`: the scalar-read prefix arithmetic (slot*120, term*4, two adds, +4) is ok for
  slot < 4, term < 26, and what remains of the read is the bounds-checked range index, try_from,
  two unwraps and the M31 decode (no checked arithmetic). `read_canon`: a successful read is < P.
- `update_ok`: the 8 checked u64 products and adds of one term are ok on canonical g, a
  canonical scalar and Bound sums n with n < 4, and give Bound (n+1).
- `inner_ok`, `inner_step`, `inner_entry`: on InnerInv the inner body is ok whenever the read
  of the current term succeeds (so its only possible failures are the read's non-arithmetic
  steps), a successful step keeps InnerInv, and the outer body enters with InnerInv.
- `outer_ops`, `outer_step`, `outer_entry`: on OuterInv the outer body's checked start + 4 is ok,
  the inner loop is entered on InnerInv and the fold of any inner result is ok; a successful
  step keeps OuterInv; four_dots_one enters with OuterInv (value 0, zero limbs).
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Dots
open Aeneas Aeneas.Std Result ControlFlow

abbrev Coeffs := Array FIo_Native.aspis_core.field.wide_exact.WideExact 29#usize

theorem umul (x y : Usize) (h : x.val * y.val ≤ 65536) :
    ∃ z, (x * y : Result Usize) = ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) (by scalar_tac))
  exact ⟨z, hz, by simpa using hv⟩

theorem uadd (x y : Usize) (h : x.val + y.val ≤ 65536) :
    ∃ z, (x + y : Result Usize) = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  exact ⟨z, hz, by simpa using hv⟩

/-! ### four_dots_one: its own checked operations on slot < 4 -/

theorem slot_ops (slot : Usize) (hs : slot.val < 4) :
    ∃ i8 i9 i10 i11 i12 i13 o0 i14 i15 i17 o1 i18 i19 : Usize,
      slot * 120#usize = ok i8 ∧ i8 + 104#usize = ok i9 ∧ i8 + 120#usize = ok i10 ∧
      slot * 32#usize = ok i11 ∧ 480#usize + i11 = ok i12 ∧ 0#usize * 16#usize = ok i13 ∧
      i12 + i13 = ok o0 ∧ 0#usize + 26#usize = ok i14 ∧ o0 + 16#usize = ok i15 ∧
      1#usize * 16#usize = ok i17 ∧ i12 + i17 = ok o1 ∧
      1#usize + 26#usize = ok i18 ∧ o1 + 16#usize = ok i19 ∧ i10.val ≤ 480 ∧ i19.val ≤ 608 := by
  obtain ⟨i8, h8, v8⟩ := umul slot 120#usize (by scalar_tac)
  obtain ⟨i9, h9, v9⟩ := uadd i8 104#usize (by scalar_tac)
  obtain ⟨i10, h10, v10⟩ := uadd i8 120#usize (by scalar_tac)
  obtain ⟨i11, h11, v11⟩ := umul slot 32#usize (by scalar_tac)
  obtain ⟨i12, h12, v12⟩ := uadd 480#usize i11 (by scalar_tac)
  obtain ⟨i13, h13, v13⟩ := umul 0#usize 16#usize (by scalar_tac)
  obtain ⟨o0, h0, w0⟩ := uadd i12 i13 (by scalar_tac)
  obtain ⟨i14, h14, v14⟩ := uadd 0#usize 26#usize (by scalar_tac)
  obtain ⟨i15, h15, v15⟩ := uadd o0 16#usize (by scalar_tac)
  obtain ⟨i17, h17, v17⟩ := umul 1#usize 16#usize (by scalar_tac)
  obtain ⟨o1, h1, w1⟩ := uadd i12 i17 (by scalar_tac)
  obtain ⟨i18, h18, v18⟩ := uadd 1#usize 26#usize (by scalar_tac)
  obtain ⟨i19, h19, v19⟩ := uadd o1 16#usize (by scalar_tac)
  exact ⟨i8, i9, i10, i11, i12, i13, o0, i14, i15, i17, o1, i18, i19, h8, h9, h10, h11, h12, h13,
    h0, h14, h15, h17, h1, h18, h19, by scalar_tac, by scalar_tac⟩

/-! ### Inner body: the scalar read and the term update -/

theorem read_arith (q : Array U8 608#usize) (slot term : Usize) (hs : slot.val < 4)
    (ht : term.val < 26) :
    ∃ i i1 i2 i4 : Usize, slot * 120#usize = ok i ∧ term * 4#usize = ok i1 ∧ i + i1 = ok i2 ∧
      i2 + 4#usize = ok i4 ∧ i4.val = 120 * slot.val + 4 * term.val + 4 ∧
      JFr_TX2_ScalarRead.read q slot term =
        (do let s ← core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=i2,«end»:=i4}
            let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
            let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
            let o ← FIp_DotDecode.field.M31.from_le_bytes a
            core.option.Option.unwrap o) := by
  obtain ⟨i, h0, v0⟩ := umul slot 120#usize (by scalar_tac)
  obtain ⟨i1, h1, v1⟩ := umul term 4#usize (by scalar_tac)
  obtain ⟨i2, h2, v2⟩ := uadd i i1 (by scalar_tac)
  obtain ⟨i4, h4, v4⟩ := uadd i2 4#usize (by scalar_tac)
  refine ⟨i, i1, i2, i4, h0, h1, h2, h4, by scalar_tac, ?_⟩
  simp only [JFr_TX2_ScalarRead.read, h0, h1, h2, h4, bind_tc_ok]

theorem read_canon (q : Array U8 608#usize) (slot term : Usize) (v : U32)
    (h : JFr_TX2_ScalarRead.read q slot term = ok v) : v.val < 2147483647 := by
  unfold JFr_TX2_ScalarRead.read at h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨a, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨o, ho, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  cases o with
  | none => cases h
  | some w =>
    have hw : w = v := Result.ok.inj (show (ok w : Result U32) = ok v from h)
    subst hw
    exact JFr_TX2_ScalarCanon.source a w ho

theorem update_ok (g : Coeffs) (hg : NEV_DotInputs.Canonical g) (term : Usize)
    (ht : term.val < 26) (scalar : U32) (hc : scalar.val < 2147483647)
    (sums : Array U64 8#usize) (n : Nat) (hn : n < 4) (hs : JFs_TX2_ArrayEight.Bound sums n) :
    ∃ out, JFr_TX2_DotStep.update g term scalar sums = ok out ∧
      JFs_TX2_ArrayEight.Bound out (n+1) := by
  have h29 : term.val < 29 := by omega
  have inRange : term.val < g.val.length := by rw [g.property]; exact h29
  obtain ⟨value, hv, _⟩ := WP.spec_imp_exists (Array.index_usize_spec g term inRange)
  have canon := NEV_DotInputs.selected g hg term h29 value hv
  obtain ⟨words, hw, hwc⟩ := NEV_DotInputs.limbs value canon
  have cw : JFs_TX2_ArrayEight.Canon words := by
    intro x hx
    have := hwc x hx
    unfold JFr_TX2_DotBounds.P
    exact this
  have cs : scalar.val < JFr_TX2_DotBounds.P := by unfold JFr_TX2_DotBounds.P; exact hc
  obtain ⟨out, run, bound⟩ := JFs_TX2_ArrayEight.source words scalar sums n cw cs hn hs
  refine ⟨out, ?_, bound⟩
  rw [JFr_TX2_DotLanes.update, hv, bind_tc_ok, hw, bind_tc_ok, run]

/-! ### Inner loop: invariant, body, step and entry -/

abbrev IState := core.ops.range.Range Usize × Array U64 8#usize

def InnerInv (base : Nat) (st : IState) : Prop :=
  st.1.end.val ≤ 26 ∧ st.1.end.val ≤ base + 4 ∧ base ≤ st.1.start.val ∧
    JFs_TX2_ArrayEight.Bound st.2 (st.1.start.val - base)

theorem inner_ok (q : Array U8 608#usize) (g : Coeffs) (slot : Usize) (base : Nat)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (hg : NEV_DotInputs.Canonical g) (inv : InnerInv base (iter, sums))
    (active : iter.start.val < iter.end.val) (v : U32)
    (hread : JFr_TX2_ScalarRead.read q slot iter.start = ok v) :
    ∃ next out, FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums =
      ok (cont (next, out)) ∧ InnerInv base (next, out) := by
  unfold InnerInv at inv
  obtain ⟨he, hw, hb, hbound⟩ := inv
  dsimp only at he hw hb hbound
  obtain ⟨out, run, bound⟩ := update_ok g hg iter.start (by omega) v
    (read_canon q slot iter.start v hread) sums (iter.start.val - base) (by omega) hbound
  obtain ⟨⟨o,next⟩,step,ho,inc,finish⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      iter active)
  subst o
  refine ⟨next, out, ?_, ?_⟩
  · rw [JFr_TX2_DotStep.body]
    simp only [JFr_TX2_DotStep.step, step, bind_tc_ok, Aeneas.Std.uncurry, hread, run]
  · have he' : next.end.val = iter.end.val := congrArg UScalar.val finish
    have inc' : next.start.val = iter.start.val + 1 := inc
    unfold InnerInv
    dsimp only
    refine ⟨by omega, by omega, by omega, ?_⟩
    have e : next.start.val - base = iter.start.val - base + 1 := by omega
    show JFs_TX2_ArrayEight.Bound out (next.start.val - base)
    rw [e]
    exact bound

theorem inner_step (q : Array U8 608#usize) (g : Coeffs) (slot : Usize) (base : Nat)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (hg : NEV_DotInputs.Canonical g) (inv : InnerInv base (iter, sums))
    (next : core.ops.range.Range Usize) (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums =
      ok (cont (next, out))) : InnerInv base (next, out) := by
  have run' := run
  rw [JFr_TX2_DotStep.body] at run'
  unfold JFr_TX2_DotStep.step at run'
  obtain ⟨⟨o,cursor⟩,hn,run'⟩ := Port3_PushFrame.bind_success _ _ _ run'
  cases o with
  | none => cases run'
  | some term =>
    obtain ⟨a,ha,_⟩ := Port3_PushFrame.bind_success _ _ _ run'
    have pr := FIo_RangeNext.some_next iter cursor term hn
    rw [pr.1] at ha
    obtain ⟨next', out', hbody, hinv⟩ := inner_ok q g slot base iter sums hg inv pr.2.2.2 a ha
    have e := Result.ok.inj (hbody.symm.trans run)
    simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hinv

theorem inner_entry (start : Usize) (h : start.val < 26) :
    ∃ end4 stop, start + 4#usize = ok end4 ∧
      core.cmp.min core.cmp.OrdUsize end4 26#usize = ok stop ∧
      InnerInv start.val ({start := start, «end» := stop}, Array.repeat 8#usize 0#u64) := by
  obtain ⟨end4, stop, h4, hm, _, a2, a3, _⟩ := JFs_TX2_BatchWindow.source start h
  refine ⟨end4, stop, h4, hm, ?_⟩
  unfold InnerInv
  refine ⟨a2, a3, le_refl _, ?_⟩
  show JFs_TX2_ArrayEight.Bound (Array.repeat 8#usize 0#u64) (start.val - start.val)
  rw [Nat.sub_self]
  exact JFs_TX2_BatchWindow.zero

/-! ### Outer StepBy loop: invariant, body operations, step and entry -/

abbrev OState := JFs_TX2_Iterator.Iter × Array U64 8#usize

def OuterInv (st : OState) : Prop :=
  ∃ k : Nat, k ≤ 7 ∧ st.1.iter.start.val = min (4 * k) 26 ∧ st.1.iter.end.val = 26 ∧
    st.1.step_by.val = 4 ∧ JFs_TX2_FoldEight.Bound st.2 k

theorem outer_ops (iter : JFs_TX2_Iterator.Iter) (limbs : Array U64 8#usize)
    (inv : OuterInv (iter, limbs)) (active : iter.iter.start.val < iter.iter.end.val) :
    ∃ end4 stop, iter.iter.start + 4#usize = ok end4 ∧
      core.cmp.min core.cmp.OrdUsize end4 26#usize = ok stop ∧
      InnerInv iter.iter.start.val ({start := iter.iter.start, «end» := stop}, Array.repeat 8#usize 0#u64) ∧
      ∀ sums, ∃ out, JFs_TX2_FoldEight.eight sums limbs = ok out := by
  unfold OuterInv at inv
  obtain ⟨k, hk, hstart, hend, _, hbound⟩ := inv
  have hs : iter.iter.start.val < 26 := by
    have h1 : iter.iter.start.val < iter.iter.end.val := active
    have h2 : iter.iter.end.val = 26 := hend
    omega
  have hk7 : k < 7 := by
    have h1 : iter.iter.start.val = min (4 * k) 26 := hstart
    omega
  obtain ⟨end4, stop, h4, hm, hi⟩ := inner_entry iter.iter.start hs
  refine ⟨end4, stop, h4, hm, hi, fun sums => ?_⟩
  obtain ⟨out, h, _⟩ := JFs_TX2_FoldEight.source sums limbs k hk7 hbound
  exact ⟨out, h⟩

theorem outer_step (q : Array U8 608#usize) (g : Coeffs) (slot : Usize)
    (iter : JFs_TX2_Iterator.Iter) (limbs : Array U64 8#usize) (inv : OuterInv (iter, limbs))
    (next : JFs_TX2_Iterator.Iter) (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs =
      ok (cont (next, out))) : OuterInv (next, out) := by
  unfold OuterInv at inv
  obtain ⟨k, hk, hstart, hend, hstep, hbound⟩ := inv
  have hstart' : iter.iter.start.val = min (4 * k) 26 := hstart
  have hend' : iter.iter.end.val = 26 := hend
  have hstep' : iter.step_by.val = 4 := hstep
  have hbound' : JFs_TX2_FoldEight.Bound limbs k := hbound
  rw [JFs_TX2_OuterStep.body] at run
  unfold JFs_TX2_OuterStep.step at run
  obtain ⟨⟨o, nx⟩, hn, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  by_cases active : iter.iter.start.val < iter.iter.end.val
  · obtain ⟨nx', hn', hs', he', hst'⟩ := JFs_TX2_Iterator.next iter hstep' active
    rw [hn'] at hn
    have e := Result.ok.inj hn
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨_, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨sums, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨out', hout, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have e2 := Result.ok.inj run
    simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    have hk7 : k < 7 := by omega
    obtain ⟨out'', h'', b''⟩ := JFs_TX2_FoldEight.source sums limbs k hk7 hbound'
    have same : out'' = out' := Result.ok.inj (h''.symm.trans hout)
    subst same
    unfold OuterInv
    refine ⟨k + 1, by omega, ?_, ?_, hst', b''⟩
    · show nx'.iter.start.val = min (4 * (k + 1)) 26
      rw [hs', hstart', hend']
      omega
    · show nx'.iter.end.val = 26
      rw [he']
      exact hend'
  · rw [JFs_TX2_Iterator.stopped iter (by omega)] at hn
    have e := Result.ok.inj hn
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    cases run

theorem outer_entry :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize,«end»:=26#usize} 4#usize = ok (JFs_TX2_Iterator.value 0) ∧
    OuterInv (JFs_TX2_Iterator.value 0, Array.repeat 8#usize 0#u64) := by
  refine ⟨JFs_TX2_Iterator.initial, ?_⟩
  unfold OuterInv
  refine ⟨0, by omega, ?_, rfl, rfl, ?_⟩
  · have h := JFs_TX2_Iterator.start ⟨0, by decide⟩
    show (JFs_TX2_Iterator.cursor 0).val = min (4 * 0) 26
    simpa using h
  · intro x hx
    change x ∈ List.replicate 8 (0#u64) at hx
    have same : x = 0#u64 := (List.mem_replicate.mp hx).2
    subst x
    simp

/-! ### Caller domain at the op20 sites -/

/-- tx1: the 094 packet carries canonical dots coefficients for the op20 call. -/
theorem tx1_g {proof : Slice U8} {p : AspisR1Stage2.verifier.Prepared}
    {g : Array FIp_DotsAdapter.E 29#usize} {geo : AspisR1Stage2.verifier.QueryGeometry}
    {start : Nat} {finish : Usize} {a : AspisR1Stage2.verifier.Accumulator}
    {b : AspisR1Stage2.verifier.BatchedWeights}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b) :
    NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g) := d.gCanonical

/-- The adapter passes toArray g unchanged to four_dots, which calls four_dots_one on it with
the literal slots 0..3. -/
theorem adapter_calls (q : Slice U8) (g : Array FIp_DotsAdapter.E 29#usize) :
    FIp_DotsAdapter.dots q g =
      (do let out ← FIp_NativeDots.fast_dots.four_dots q (FIp_DotsAdapter.toArray g)
          ok (FIp_DotsAdapter.fromArray out)) ∧
    (0#usize : Usize).val < 4 ∧ (1#usize : Usize).val < 4 ∧ (2#usize : Usize).val < 4 ∧
      (3#usize : Usize).val < 4 :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

#print axioms umul
#print axioms uadd
#print axioms slot_ops
#print axioms read_arith
#print axioms read_canon
#print axioms update_ok
#print axioms inner_ok
#print axioms inner_step
#print axioms inner_entry
#print axioms outer_ops
#print axioms outer_step
#print axioms outer_entry
#print axioms tx1_g
#print axioms adapter_calls
end AspisR1.NPH_R22Dots
