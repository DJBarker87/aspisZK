import Stage2ContinuationQueryLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
abbrev Stage2K := aspis_core.field.QM31
abbrev Stage2E := aspis_core.field.wide_exact.WideExact
abbrev Stage2M := aspis_core.field.M31
structure AccumulateOps where
  zero : Result Stage2M
  one : Result Stage2M
  basisLoop : Stage2M → Stage2M → Usize → Array Stage2M 256#usize → Usize → Result (Array Stage2M 256#usize)
  weightLoop : core.ops.range.Range Usize → alloc.vec.Vec Stage2K → Stage2K → Usize → verifier.BatchedWeights → Usize → Array Stage2M 256#usize → Result verifier.BatchedWeights
  mulE : Stage2E → Stage2K → Result Stage2E
  addE : Stage2E → Stage2E → Result Stage2E
  trace : U16 → Usize → Stage2E → Result Unit
  mulK : Stage2K → Stage2K → Result Stage2K
structure QueryOps where
  opening : Slice U8 → Usize → Result (Slice U8)
  dots : Slice U8 → Array Stage2E 29#usize → Result (Array Stage2E 4#usize)
  inverse : verifier.QueryGeometry → Usize → Result (Array Stage2M 5#usize)
  circle : Stage2E → Array Stage2E 4#usize → Array Stage2M 5#usize → Result Stage2E
  values : Slice U8 → Result (Array Stage2E 4#usize)
  ne : Stage2E → Stage2E → Result Bool
  line : Stage2E → Array Stage2E 4#usize → Array Stage2M 5#usize → Result Stage2E
  mulM : Stage2M → Stage2M → Result Stage2M
  doubleM : Stage2M → Result Stage2M
  oneM : Result Stage2M
  subM : Stage2M → Stage2M → Result Stage2M
  mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit
  trace : U16 → Usize → Stage2E → Result Unit
def verifier.accumulateWithOps
  (ops : AccumulateOps)
  (p : verifier.Prepared) (a : verifier.Accumulator)
  (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
  (weights : verifier.BatchedWeights) :
  Result (verifier.Accumulator × verifier.BatchedWeights)
  := do
  let width := alloc.vec.Vec.len a.weights
  let m ← ops.zero
  let basis := Array.repeat 256#usize m
  let m1 ← ops.one
  let basis1 ← Array.update basis 0#usize m1
  let basis2 ←
    ops.basisLoop m1 node width basis1 1#usize
  let weights1 ←
    ops.weightLoop
      { start := 0#usize, «end» := width } a.weights a.power a.next weights
      width basis2
  let i ← weights1.terms + 1#usize
  let we ← ops.mulE value a.power
  let we1 ← ops.addE a.rhs we
  ops.trace 11#u16 a.next we1
  let q ← ops.mulK a.power p.rho
  let i1 ← a.next + 1#usize
  ok ({ a with rhs := we1, power := q, next := i1 },
    { weights1 with terms := i })

def verifier.candidate.queryInPlaceWithOps
  (aops : AccumulateOps) (ops : QueryOps)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
  Result ((core.result.Result Unit verifier.Error) × verifier.Accumulator ×
    verifier.BatchedWeights)
  := do
  let i ← Array.index_usize p.queries a.next
  let u ← lift (UScalar.cast .Usize i)
  let q ← ops.opening proof a.next
  let dots ← ops.dots q g
  let i1 ← 4#usize * a.next
  let we ← Array.index_usize dots 0#usize
  ops.trace 9#u16 i1 we
  let i2 ← i1 + 1#usize
  let we1 ← Array.index_usize dots 1#usize
  ops.trace 9#u16 i2 we1
  let i3 ← i1 + 2#usize
  let we2 ← Array.index_usize dots 2#usize
  ops.trace 9#u16 i3 we2
  let i4 ← i1 + 3#usize
  let we3 ← Array.index_usize dots 3#usize
  ops.trace 9#u16 i4 we3
  let inverse ← ops.inverse geometry a.next
  let we4 ← Array.index_usize p.alpha 0#usize
  let folded ← ops.circle we4 dots inverse
  let i5 ← 2#usize * a.next
  ops.trace 10#u16 i5 folded
  let values ←
    ops.values q
  let i6 ← u % 4#usize
  let we5 ← Array.index_usize values i6
  let b ←
    ops.ne folded we5
  if b
  then ok (core.result.Result.Err verifier.Error.Query, a, pending)
  else
    let we6 ← Array.index_usize p.alpha 1#usize
    let folded1 ← ops.line we6 values inverse
    let i7 ← i5 + 1#usize
    ops.trace 10#u16 i7 folded1
    let i8 ← a.next - geometry.start
    let z ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) geometry.line_z i8
    let m ← ops.mulM z z
    let m1 ← ops.doubleM m
    let m2 ← ops.oneM
    let node ← ops.subM m1 m2
    let (a1, pending1) ←
      verifier.accumulateWithOps aops p a node folded1 pending
    ops.mark obs (verifier.Phase.Query a.next)
    ok (core.result.Result.Ok (), a1, pending1)

def verifier.candidate.queryWithOps
  (aops : AccumulateOps) (ops : QueryOps)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  let (r, a1, pending1) ←
    verifier.candidate.queryInPlaceWithOps aops ops proof p a g obs geometry pending
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    ok (core.result.Result.Ok (a1, pending1))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (verifier.Accumulator × verifier.BatchedWeights) (core.convert.FromSame
      verifier.Error) residual

end AspisR1Stage2
namespace AspisR1Stage2
private theorem advance_bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem checked_add_value (x y z : Usize) (h : x + y = ok z) :
    z.val = x.val + y.val := by
  change UScalar.tryMk _ (x.val+y.val) = ok z at h
  unfold UScalar.tryMk UScalar.tryMkOpt UScalar.check_bounds at h
  split at h
  · cases h; rfl
  · cases h

theorem accumulate_next (ops : AccumulateOps) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : Stage2M) (value : Stage2E)
    (b bout : verifier.BatchedWeights)
    (h : verifier.accumulateWithOps ops p a node value b = ok (out,bout)) :
    out.next.val = a.next.val + 1 := by
  unfold verifier.accumulateWithOps at h
  obtain ⟨m, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨m1, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨basis1, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨basis2, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨weights1, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨terms, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨we, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨we1, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨traceResult, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨power, _, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨next, hnext, h⟩ := advance_bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  exact checked_add_value a.next 1#usize next hnext

private theorem query_guard (b : Bool) (a : verifier.Accumulator)
    (w : verifier.BatchedWeights)
    (tail : Result (core.result.Result Unit verifier.Error × verifier.Accumulator × verifier.BatchedWeights))
    (out : verifier.Accumulator) (bout : verifier.BatchedWeights)
    (h : (if b then ok (.Err verifier.Error.Query,a,w) else tail) =
      ok (.Ok (),out,bout)) : tail = ok (.Ok (),out,bout) := by
  cases b
  · exact h
  · cases h

theorem query_in_place_next (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.queryInPlaceWithOps aops ops proof p a g obs geometry b =
      ok (.Ok (),out,bout)) : out.next.val = a.next.val + 1 := by
  unfold verifier.candidate.queryInPlaceWithOps at h
  iterate 25 obtain ⟨x, hx, h⟩ := advance_bind_success _ _ _ h
  have h := query_guard _ _ _ _ _ _ h
  iterate 10 obtain ⟨x, hx, h⟩ := advance_bind_success _ _ _ h
  obtain ⟨pair, hacc, h⟩ := advance_bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨markResult, _, h⟩ := advance_bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  exact accumulate_next aops p a out _ _ b bout hacc

theorem query_next (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.queryWithOps aops ops proof p a g obs geometry b =
      ok (.Ok (out,bout))) : out.next.val = a.next.val + 1 := by
  unfold verifier.candidate.queryWithOps at h
  obtain ⟨triple,hcall,h⟩ := advance_bind_success _ _ _ h
  rcases triple with ⟨r,a1,b1⟩
  cases r with
  | Err e =>
    change (ok (core.result.Result.Err e) : Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)) = ok (.Ok (out,bout)) at h
    cases h
  | Ok unit =>
    cases unit
    change (ok (core.result.Result.Ok (a1,b1)) : Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)) = ok (.Ok (out,bout)) at h
    have hp := Result.ok.inj h
    cases hp
    exact query_in_place_next aops ops proof p a out g obs geometry b bout hcall

#print axioms advance_bind_success
#print axioms checked_add_value
#print axioms accumulate_next
#print axioms query_guard
#print axioms query_in_place_next
#print axioms query_next
end AspisR1Stage2
