import R17QueryValuesEntryActualDefsV1

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17QueryValuesWholeBodyV21

open AspisR1QueryGeometryActual
open R17QueryValuesEntryActualV1

abbrev SourceError := QueryValuesError

structure SourceCallees where
  fibrePoint : domain.FibreIndex → Result (domain.Point field.M31)
  lineNode : domain.FibreIndex → Result field.M31
  mul : field.M31 → field.M31 → Result field.M31
  double : field.M31 → Result field.M31
  sub : field.M31 → field.M31 → Result field.M31
  one : field.M31



def core.result.Result.map_err
    {T E F O : Type} (fn : core.ops.function.FnOnce O E F)
    (self : core.result.Result T E) (op : O) :
    Result (core.result.Result T F) := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
      let t ← fn.call_once op e
      ok (core.result.Result.Err t)

def sourceErrorCallOnce (_c : Unit) (_ : SourceError) : Result SourceError :=
  ok QueryValuesError.Query

def sourceErrorMapFnOnce : core.ops.function.FnOnce Unit SourceError SourceError :=
  { call_once := sourceErrorCallOnce }

def rawMapBranch {α β : Type}
    (fn : core.ops.function.FnOnce Unit SourceError SourceError)
    (r : core.result.Result α SourceError)
    (k : α → Result (core.result.Result β SourceError)) :
    Result (core.result.Result β SourceError) := do
  let r1 ← core.result.Result.map_err fn r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => k val
  | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        β (core.convert.FromSame SourceError) residual

theorem rawMapBranch_eq_sourceMapTry
    {α β : Type}
    (fn : core.ops.function.FnOnce Unit SourceError SourceError)
    (r : core.result.Result α SourceError)
    (k : α → Result (core.result.Result β SourceError)) :
    rawMapBranch fn r k =
      sourceMapTryFromResidual (fun e => fn.call_once () e) r k := by
  cases r with
  | Ok a => rfl
  | Err e =>
      cases hf : fn.call_once () e <;>
        simp [rawMapBranch, sourceMapTryFromResidual, core.result.Result.map_err,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, hf]
      all_goals rfl

#print axioms rawMapBranch_eq_sourceMapTry

def emittedRawWithCallees (cs : SourceCallees) (anyCheck : core.slice.iter.Iter field.M31 → Result (Bool × core.slice.iter.Iter field.M31))
  (query : Std.U32) :
  Result (core.result.Result ((Array field.M31 5#usize) × field.M31) SourceError)
  := do
  let u ← lift (UScalar.cast .Usize query)
  let r ← R17QueryValuesEntryActualV1.fibreIndexNew u
  let r1 ←
    core.result.Result.map_err
      sourceErrorMapFnOnce
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let point ← cs.fibrePoint val
    let i ← u / 4#usize
    let i1 ← i * 4#usize
    let r2 ← R17QueryValuesEntryActualV1.fibreIndexNew i1
    let r3 ←
      core.result.Result.map_err
        sourceErrorMapFnOnce
        r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let line_x ← cs.lineNode val1
      let i2 ← i * 4#usize
      let i3 ← i2 + 3#usize
      let r4 ← R17QueryValuesEntryActualV1.fibreIndexNew i3
      let r5 ←
        core.result.Result.map_err
          sourceErrorMapFnOnce
          r4 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let line_y ← cs.lineNode val2
        let m ← cs.mul line_x line_x
        let m1 ← cs.double m
        let line_z ← cs.sub m1 cs.one
        let s ←
          lift (Array.to_slice
            (Array.make 5#usize [ point.x, point.y, line_x, line_y, line_z ]))
        let i4 ← core.slice.Slice.iter s
        let (b, _) ←
          anyCheck i4
        if b
        then ok (core.result.Result.Err QueryValuesError.Query)
        else
          ok (core.result.Result.Ok
            (Array.make 5#usize [ point.x, point.y, line_x, line_y, line_z ],
            line_z))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array field.M31 5#usize) × field.M31) (core.convert.FromSame
          SourceError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array field.M31 5#usize) × field.M31) (core.convert.FromSame SourceError)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array field.M31 5#usize) × field.M31) (core.convert.FromSame SourceError)
      residual


def directWithCallees (cs : SourceCallees) (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    Result (core.result.Result ((Array field.M31 5#usize) × field.M31) SourceError) := do
  let u ← lift (UScalar.cast .Usize q)
  let r ← R17QueryValuesEntryActualV1.fibreIndexNew u
  sourceDirectMatch (fun _ => pure QueryValuesError.Query) r (fun val => do
    let point ← cs.fibrePoint val
    let i ← u / 4#usize
    let i1 ← i * 4#usize
    let r1 ← R17QueryValuesEntryActualV1.fibreIndexNew i1
    sourceDirectMatch (fun _ => pure QueryValuesError.Query) r1 (fun val1 => do
      let line_x ← cs.lineNode val1
      let i2 ← i * 4#usize
      let i3 ← i2 + 3#usize
      let r2 ← R17QueryValuesEntryActualV1.fibreIndexNew i3
      sourceDirectMatch (fun _ => pure QueryValuesError.Query) r2 (fun val2 => do
        let line_y ← cs.lineNode val2
        let m ← cs.mul line_x line_x
        let m1 ← cs.double m
        let line_z ← cs.sub m1 cs.one
        let sl ← lift (Array.to_slice
          (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z]))
        let it ← core.slice.Slice.iter sl
        let (b, _) ← anyCheck it
        if b then ok (core.result.Result.Err QueryValuesError.Query)
        else ok (core.result.Result.Ok (Array.make 5#usize
          [point.x, point.y, line_x, line_y, line_z], line_z)))
    ))

theorem rawMapBranch_expand {α β : Type}
    (fn : core.ops.function.FnOnce Unit SourceError SourceError)
    (r : core.result.Result α SourceError)
    (k : α → Result (core.result.Result β SourceError)) :
    rawMapBranch fn r k = (do
      let r1 ← core.result.Result.map_err fn r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => k val
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            β (core.convert.FromSame SourceError) residual) := rfl

def loweredWithCallees (cs : SourceCallees)
    (anyCheck : core.slice.iter.Iter field.M31 → Result (Bool × core.slice.iter.Iter field.M31))
    (query : Std.U32) :
    Result (core.result.Result ((Array field.M31 5#usize) × field.M31) SourceError) := do
  let u ← lift (UScalar.cast .Usize query)
  let r ← R17QueryValuesEntryActualV1.fibreIndexNew u
  rawMapBranch sourceErrorMapFnOnce r (fun val => do
    let point ← cs.fibrePoint val
    let i ← u / 4#usize
    let i1 ← i * 4#usize
    let r1 ← R17QueryValuesEntryActualV1.fibreIndexNew i1
    rawMapBranch sourceErrorMapFnOnce r1 (fun val1 => do
      let line_x ← cs.lineNode val1
      let i2 ← i * 4#usize
      let i3 ← i2 + 3#usize
      let r2 ← R17QueryValuesEntryActualV1.fibreIndexNew i3
      rawMapBranch sourceErrorMapFnOnce r2 (fun val2 => do
        let line_y ← cs.lineNode val2
        let m ← cs.mul line_x line_x
        let m1 ← cs.double m
        let line_z ← cs.sub m1 cs.one
        let sl ← lift (Array.to_slice
          (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z]))
        let it ← core.slice.Slice.iter sl
        let (b, _) ← anyCheck it
        if b then ok (core.result.Result.Err QueryValuesError.Query)
        else ok (core.result.Result.Ok (Array.make 5#usize
          [point.x, point.y, line_x, line_y, line_z], line_z)))))

private theorem bind_congr_local {α β : Type} (m : Result α)
    (k l : α → Result β) (h : ∀ x, k x = l x) :
    (do let x ← m; k x) = (do let x ← m; l x) := by
  cases m with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

private theorem rawSequence_congr {α β : Type}
    (fn : core.ops.function.FnOnce Unit SourceError SourceError)
    (r : core.result.Result α SourceError)
    (k l : α → Result (core.result.Result β SourceError))
    (h : ∀ x, k x = l x) :
    (do
      let r1 ← core.result.Result.map_err fn r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => k val
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            β (core.convert.FromSame SourceError) residual) =
      rawMapBranch fn r l := by
  rw [rawMapBranch_expand]
  apply bind_congr_local
  intro r1
  apply bind_congr_local
  intro cf
  cases cf with
  | Continue val => exact h val
  | Break residual => rfl

theorem emittedRaw_eq_lowered
    (cs : SourceCallees) (query : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    emittedRawWithCallees cs anyCheck query = loweredWithCallees cs anyCheck query := by
  unfold emittedRawWithCallees loweredWithCallees
  simp only [rawMapBranch_expand]
  apply bind_congr_local
  intro u
  apply bind_congr_local
  intro r
  apply bind_congr_local
  intro r1
  apply bind_congr_local
  intro cf
  cases cf with
  | Continue val =>
    apply bind_congr_local
    intro point
    apply bind_congr_local
    intro i
    apply bind_congr_local
    intro i1
    apply bind_congr_local
    intro r2
    apply bind_congr_local
    intro r3
    apply bind_congr_local
    intro cf1
    cases cf1 with
    | Continue val1 =>
      apply bind_congr_local
      intro lineX
      apply bind_congr_local
      intro i2
      apply bind_congr_local
      intro i3
      apply bind_congr_local
      intro r4
      apply bind_congr_local
      intro r5
      apply bind_congr_local
      intro cf2
      cases cf2 with
      | Continue val2 =>
        apply bind_congr_local
        intro lineY
        apply bind_congr_local
        intro m
        apply bind_congr_local
        intro m1
        apply bind_congr_local
        intro lineZ
        apply bind_congr_local
        intro sl
        apply bind_congr_local
        intro it
        apply bind_congr_local
        intro resultAny
        rcases resultAny with ⟨b, it2⟩
        rfl
      | Break residual => rfl
    | Break residual => rfl
  | Break residual => rfl

private theorem sourceDirectMatch_congr {α β : Type}
    (f : SourceError → Result SourceError)
    (r : core.result.Result α SourceError)
    (k l : α → Result (core.result.Result β SourceError))
    (h : ∀ x, k x = l x) :
    sourceDirectMatch f r k = sourceDirectMatch f r l := by
  cases r with
  | Ok a => exact h a
  | Err e => rfl

private theorem rawMapBranch_congr {α β : Type}
    (r : core.result.Result α SourceError)
    (k l : α → Result (core.result.Result β SourceError))
    (h : ∀ x, k x = l x) :
    rawMapBranch sourceErrorMapFnOnce r k =
      sourceDirectMatch (fun _ => pure QueryValuesError.Query) r l := by
  rw [rawMapBranch_eq_sourceMapTry,
    R17QueryValuesEntryActualV1.sourceMapTryFromResidual_eq_directMatch]
  exact sourceDirectMatch_congr _ _ _ _ h

theorem lowered_eq_direct
    (cs : SourceCallees) (query : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    loweredWithCallees cs anyCheck query = directWithCallees cs query anyCheck := by
  unfold loweredWithCallees directWithCallees
  apply bind_congr_local
  intro u
  apply bind_congr_local
  intro r
  apply rawMapBranch_congr
  intro val
  apply bind_congr_local
  intro point
  apply bind_congr_local
  intro i
  apply bind_congr_local
  intro i1
  apply bind_congr_local
  intro r1
  apply rawMapBranch_congr
  intro val1
  apply bind_congr_local
  intro lineX
  apply bind_congr_local
  intro i2
  apply bind_congr_local
  intro i3
  apply bind_congr_local
  intro r2
  apply rawMapBranch_congr
  intro val2
  rfl

theorem emittedRawWithCallees_eq_directWithCallees
    (cs : SourceCallees) (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    emittedRawWithCallees cs anyCheck q = directWithCallees cs q anyCheck := by
  rw [emittedRaw_eq_lowered, lowered_eq_direct]

#print axioms emittedRawWithCallees_eq_directWithCallees


end R17QueryValuesWholeBodyV21
