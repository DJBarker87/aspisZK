import CurrentClaimSumTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim

structure ClaimDotOps (D : Type) where
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  field : Slice U8 → Usize → Result aspis_core.field.WideExact
  c0 : aspis_core.field.WideExact → Result aspis_core.field.QM31
  newDot : Result D
  pushDot : D → aspis_core.field.WideExact → aspis_core.field.QM31 → Result (core.result.Result Unit Unit × D)
  finishDot : D → Result aspis_core.field.WideExact
/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
  Result (core.result.Result T F)
  := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
    let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err t)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::{impl core::ops::function::FnOnce<((),), aspis_r1_verify_prepared_prefix::verifier::Error> for aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::closure<H>}::call_once]:
    Source: 'lib.rs', lines 763:38-763:53 -/
def
  verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : verifier.prepared_claim_dot.closure H) (_ : Unit) :
  Result verifier.Error
  := do
  ok verifier.Error.Parse

/-- Trait implementation: [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::{impl core::ops::function::FnOnce<((),), aspis_r1_verify_prepared_prefix::verifier::Error> for aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::closure<H>}]
    Source: 'lib.rs', lines 763:38-763:53 -/
@[reducible]
def
  verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (verifier.prepared_claim_dot.closure H) Unit
  verifier.Error := {
  call_once :=
    verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once
    aspis_coreDigest32Inst
}

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot]: loop body 0:
    Source: 'lib.rs', lines 761:4-766:1 -/
@[rust_loop_body]
def verifier.prepared_claim_dot_loop.body
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (y1 : Slice Std.U8) (g : Array aspis_core.field.WideExact 29#usize)
  (iter : core.ops.range.Range Std.Usize) (sem : r1_semantic.Verified H)
  (point : Std.Usize) (dot : D) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    (r1_semantic.Verified H) × Std.Usize × D)
    (core.result.Result aspis_core.field.WideExact verifier.Error))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let we ← ops.finishDot dot
    ok (done (core.result.Result.Ok we))
  | some l =>
    let (sem1, point1, iter2, scalar) ←
      if 0#usize <= point
      then
        if point <= 2#usize
        then
          do
          let a ← Array.index_usize sem.claims point
          let scalar1 ← Array.index_usize a l
          ok (sem, point, iter1, scalar1)
        else
          do
          let (v, q) ←
            match point.val with
            | 3 =>
              do
              let scalar1 ← Array.index_usize sem.extra l
              ok (sem, scalar1)
            | 4 =>
              do
              let scalar1 ← Array.index_usize sem.before_z1 l
              ok (sem, scalar1)
            | _ =>
              do
              let we ← ops.field y1 l
              let scalar1 ← ops.c0 we
              ok (sem, scalar1)
          ok (v, point, iter1, q)
      else
        do
        let (v, q) ←
          match point.val with
          | 3 =>
            do
            let scalar1 ← Array.index_usize sem.extra l
            ok (sem, scalar1)
          | 4 =>
            do
            let scalar1 ← Array.index_usize sem.before_z1 l
            ok (sem, scalar1)
          | _ =>
            do
            let we ← ops.field y1 l
            let scalar1 ← ops.c0 we
            ok (sem, scalar1)
        ok (v, point, iter1, q)
    let we ← Array.index_usize g l
    let (r, dot1) ← ops.pushDot dot we scalar
    let r1 ←
      core.result.Result.map_err
        (verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError
        aspis_coreDigest32Inst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (cont (iter2, sem1, point1, dot1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.WideExact (core.convert.FromSame verifier.Error)
          residual
      ok (done r2)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot]: loop 0:
    Source: 'lib.rs', lines 761:4-766:1 -/
@[rust_loop]
def verifier.prepared_claim_dot_loop
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (iter : core.ops.range.Range Std.Usize) (sem : r1_semantic.Verified H)
  (y1 : Slice Std.U8) (g : Array aspis_core.field.WideExact 29#usize)
  (point : Std.Usize) (dot : D) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  loop
    (fun (iter1, sem1, point1, dot1) => verifier.prepared_claim_dot_loop.body ops
      aspis_coreDigest32Inst y1 g iter1 sem1 point1 dot1)
    (iter, sem, point, dot)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot]:
    Source: 'lib.rs', lines 759:0-766:1 -/
def verifier.prepared_claim_dot
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Slice Std.U8)
  (g : Array aspis_core.field.WideExact 29#usize) (point : Std.Usize) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  let dot ← ops.newDot
  verifier.prepared_claim_dot_loop ops aspis_coreDigest32Inst
    { start := 0#usize, «end» := 29#usize } sem y1 g point dot

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim]: loop body 0:
    Source: 'lib.rs', lines 770:8-774:1 -/
@[rust_loop_body]
def verifier.prepared_claim_loop.body
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Slice Std.U8)
  (g : Array aspis_core.field.WideExact 29#usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (iter : core.ops.range.Range Std.Usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.WideExact 7#usize)) (core.result.Result
    aspis_core.field.WideExact verifier.Error))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let we ← verifier.prepared_claim_sum k parts
    ok (done (core.result.Result.Ok we))
  | some point =>
    let r ← verifier.prepared_claim_dot ops aspis_coreDigest32Inst sem y1 g point
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← point + 1#usize
      let a ← Array.update parts i val
      ok (cont (iter1, a))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.WideExact (core.convert.FromSame verifier.Error)
          residual
      ok (done r1)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim]: loop 0:
    Source: 'lib.rs', lines 770:8-774:1 -/
@[rust_loop]
def verifier.prepared_claim_loop
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (iter : core.ops.range.Range Std.Usize) (sem : r1_semantic.Verified H)
  (y1 : Slice Std.U8) (g : Array aspis_core.field.WideExact 29#usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  loop
    (fun (iter1, parts1) => verifier.prepared_claim_loop.body ops
      aspis_coreDigest32Inst sem y1 g k iter1 parts1)
    (iter, parts)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim]:
    Source: 'lib.rs', lines 767:0-774:1 -/
def verifier.prepared_claim
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Slice Std.U8)
  (inactive : aspis_core.field.WideExact)
  (g : Array aspis_core.field.WideExact 29#usize)
  (kappa : aspis_core.field.WideExact) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  let k ← ops.powers 7#usize kappa
  let parts := Array.repeat 7#usize aspis_core.field.WideExact.ZERO
  let a ← Array.update parts 0#usize inactive
  verifier.prepared_claim_loop ops aspis_coreDigest32Inst
    { start := 0#usize, «end» := 6#usize } sem y1 g k a


#print axioms verifier.prepared_claim_dot_loop.body
#print axioms verifier.prepared_claim_dot_loop
#print axioms verifier.prepared_claim_dot
#print axioms verifier.prepared_claim_loop.body
#print axioms verifier.prepared_claim_loop
#print axioms verifier.prepared_claim
end AspisR1CurrentPreparedClaim
