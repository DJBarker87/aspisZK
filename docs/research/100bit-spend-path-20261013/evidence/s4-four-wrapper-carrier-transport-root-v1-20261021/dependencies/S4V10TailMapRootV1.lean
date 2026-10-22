import S4V10HeadLoopBoundV1
import AspisR1FastDotsCurrent.FunsOpsFixedV6
import S4FixedTailProgramEqualityRootV1

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10TailMapRootV1
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1
open AspisR1FastDotsV10HeadLoopBoundV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev V10QM := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.QM31
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev U32 := Aeneas.Std.U32

 def mapRes {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div

theorem mapRes_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    mapRes f (r >>= k) = r >>= fun x => mapRes f (k x) := by
  cases r <;> rfl

private theorem mapRes_injective {A B : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a) = a) : Function.Injective (mapRes f) := by
  intro x y heq
  cases x with
  | ok a =>
    cases y with
    | ok b =>
      have h' : f a = f b := by simpa [mapRes] using heq
      have hh := congrArg g h'
      simpa [h a, h b] using hh
    | fail e => simp [mapRes] at heq
    | div => simp [mapRes] at heq
  | fail e =>
    cases y with
    | ok b => simp [mapRes] at heq
    | fail e' => cases heq; rfl
    | div => simp [mapRes] at heq
  | div =>
    cases y with
    | ok b => simp [mapRes] at heq
    | fail e => simp [mapRes] at heq
    | div => rfl

private theorem mapRes_comp_id {A B : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a) = a) (r : Result A) : mapRes g (mapRes f r) = r := by
  cases r with
  | ok a => simp [mapRes, h a]
  | fail e => rfl
  | div => rfl

theorem mapRes_pairLet {A B C D : Type} (f : C → D) (p : A × B)
    (k : A → B → Result C) :
    mapRes f (let (a,b) := p; k a b) = let (a,b) := p; mapRes f (k a b) := by
  cases p <;> rfl

theorem mapRes_bind_pairLet {A B C D : Type} (f : C → D)
    (r : Result (A × B)) (k : A → B → Result C) :
    mapRes f (r >>= fun p => let (a,b) := p; k a b) =
      r >>= fun p => let (a,b) := p; mapRes f (k a b) := by
  cases r with
  | ok p => cases p <;> rfl
  | fail e => rfl
  | div => rfl

private theorem bind_congr_right {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x = g x) :
    (r >>= f) = (r >>= g) := by
  cases r with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

private theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((r >>= f) >>= g) = (r >>= fun x => f x >>= g) := by
  cases r <;> rfl

theorem mapRes_unwrap_wide (o : Option Wide) :
    mapRes wideToEbyK (core.option.Option.unwrap (Option.map wideFromEbyK o)) =
      core.option.Option.unwrap o := by
  cases o <;> rfl

theorem mapRes_unwrap_qm (o : Option AspisR1EbyKPushCutV3.field.QM31) :
    mapRes qm31ToEbyK (core.option.Option.unwrap (Option.map qm31FromEbyK o)) =
      core.option.Option.unwrap o := by
  cases o <;> rfl

theorem unwrap_map_bind {A B C : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a) = a) (o : Option A) (k : A → Result C) :
    (core.option.Option.unwrap (Option.map f o) >>= fun b => k (g b)) =
      (core.option.Option.unwrap o >>= k) := by
  cases o with
  | none => rfl
  | some a => simp [core.option.Option.unwrap, h a]

def v10FromLimbs (ops : CurrentOps) (limbs : Array U32 8#usize) :
    Result (Option V10Wide) := do
  let o ← ops.wideFromLimbs limbs
  ok (o.map wideFromEbyK)

def v10QMFromBytes (ops : CurrentOps) (s : Slice Std.U8) : Result (Option V10QM) := do
  let o ← ops.qm31FromBytes s
  ok (o.map qm31FromEbyK)

def v10Push (ops : CurrentOps) (tail : AspisR1FastDotsCurrent.fast_pairing.EbyKDot)
    (w : V10Wide) (q : V10QM) :
    Result ((core.result.Result Unit Unit) × AspisR1FastDotsCurrent.fast_pairing.EbyKDot) :=
  ops.ebyKPush tail (wideToEbyK w) (qm31ToEbyK q)

def v10Finish (ops : CurrentOps) (tail : AspisR1FastDotsCurrent.fast_pairing.EbyKDot) :
    Result V10Wide := mapRes wideFromEbyK (ops.ebyKFinish tail)

def v10Add (ops : CurrentOps) (x y : V10Wide) : Result V10Wide :=
  mapRes wideFromEbyK (ops.wideAdd (wideToEbyK x) (wideToEbyK y))

def v10Tail (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) (value : V10Wide) : Result V10Wide := do
  let tail ← ops.ebyKNew
  let we ← g.index_usize 28#usize
  let i8 ← slot * 120#usize
  let i9 ← i8 + 104#usize
  let i10 ← i8 + 120#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := i9, «end» := i10 }
  let o1 ← v10QMFromBytes ops s
  let q1 ← core.option.Option.unwrap o1
  let (r,tail1) ← v10Push ops tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i11 ← slot * 32#usize
  let i12 ← 480#usize + i11
  let i13 ← 0#usize * 16#usize
  let offset0 ← i12 + i13
  let i14 ← 0#usize + 26#usize
  let we1 ← g.index_usize i14
  let i15 ← offset0 + 16#usize
  let s1 ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := offset0, «end» := i15 }
  let o2 ← v10QMFromBytes ops s1
  let q2 ← core.option.Option.unwrap o2
  let (r1,tail2) ← v10Push ops tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i16 ← 480#usize + i11
  let i17 ← 1#usize * 16#usize
  let offset1 ← i16 + i17
  let i18 ← 1#usize + 26#usize
  let we2 ← g.index_usize i18
  let i19 ← offset1 + 16#usize
  let s2 ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := offset1, «end» := i19 }
  let o3 ← v10QMFromBytes ops s2
  let q3 ← core.option.Option.unwrap o3
  let (r2,tail3) ← v10Push ops tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← v10Finish ops tail3
  v10Add ops value we3

private theorem bind_mapRes {A B C : Type} (f : A → B) (r : Result A) (k : B → Result C) :
    (mapRes f r >>= k) = (r >>= fun x => k (f x)) := by cases r <;> rfl

theorem v10Tail_to_current (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) (value : V10Wide) :
    mapRes wideToEbyK (v10Tail ops q g slot value) =
      AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail ops q
        (mapWideArray g) slot (wideToEbyK value) := by
  unfold v10Tail AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail
  simp only [v10QMFromBytes, v10Push, v10Finish, v10Add,
    mapRes_bind, mapRes_pairLet, bind_mapRes, mapRes_comp_id,
    mapWideArray_index, bind_mapResult, result_bind_assoc,
    bind_tc_ok, wide_roundtrip', qm31_roundtrip']
  repeat' (apply bind_congr_right; intro x)
  cases x with
  | none => simp only [Option.map,core.option.Option.unwrap,Result.ofOption,bind_tc_fail]
  | some q0 =>
    simp only [Option.map,core.option.Option.unwrap,Result.ofOption,bind_tc_ok,qm31_roundtrip']
    repeat' (apply bind_congr_right; intro p0)
    rcases p0 with ⟨r0,t0⟩
    change mapRes wideToEbyK (core.result.Result.unwrap core.fmt.DebugUnit r0 >>= _) =
      (core.result.Result.unwrap core.fmt.DebugUnit r0 >>= _)
    rw [mapRes_bind]
    simp only [mapRes_bind,mapRes_pairLet,bind_mapRes,result_bind_assoc,
      bind_tc_ok,wide_roundtrip']
    repeat' (apply bind_congr_right; intro o1)
    cases o1 with
    | none => simp only [bind_tc_fail]
    | some q1 =>
      simp only [bind_tc_ok,qm31_roundtrip']
      repeat' (apply bind_congr_right; intro p1)
      rcases p1 with ⟨r1,t1⟩
      change mapRes wideToEbyK (core.result.Result.unwrap core.fmt.DebugUnit r1 >>= _) =
        (core.result.Result.unwrap core.fmt.DebugUnit r1 >>= _)
      rw [mapRes_bind]
      simp only [mapRes_bind,mapRes_pairLet,bind_mapRes,result_bind_assoc,
        bind_tc_ok,wide_roundtrip']
      repeat' (apply bind_congr_right; intro o2)
      cases o2 with
      | none => simp only [bind_tc_fail]
      | some q2 =>
        simp only [bind_tc_ok,qm31_roundtrip']
        repeat' (apply bind_congr_right; intro p2)
        rcases p2 with ⟨r2,t2⟩
        change mapRes wideToEbyK (core.result.Result.unwrap core.fmt.DebugUnit r2 >>= _) =
          (core.result.Result.unwrap core.fmt.DebugUnit r2 >>= _)
        rw [mapRes_bind]
        simp only [mapRes_bind,
          mapRes_comp_id wideFromEbyK wideToEbyK wide_roundtrip',bind_tc_ok]

#print axioms v10Tail_to_current
end AspisR1FastDotsV10TailMapRootV1
