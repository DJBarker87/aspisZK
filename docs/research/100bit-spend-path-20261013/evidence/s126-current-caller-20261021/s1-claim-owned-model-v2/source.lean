import S1ClaimAllLoopsBoundedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim
/-- Documented Result::is_err: no callbacks or state effects. -/
def ownedIsErr {T E : Type} (r : core.result.Result T E) : Result Bool :=
  ok (match r with | .Ok _ => false | .Err _ => true)

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_scalar]:
    Source: 'lib.rs', lines 753:0-753:190 -/
def verifier.owned_scalar
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (point : Std.Usize) (l : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  if 0#usize <= point
  then
    if point <= 2#usize
    then let a ← Array.index_usize claims point
         Array.index_usize a l
    else
      match point.val with
      | 3 => Array.index_usize extra l
      | 4 => Array.index_usize before_z1 l
      | _ =>
        let s ← lift (Array.to_slice y1)
        let we ← ops.field s l
        ops.c0 we
  else
    match point.val with
    | 3 => Array.index_usize extra l
    | 4 => Array.index_usize before_z1 l
    | _ =>
      let s ← lift (Array.to_slice y1)
      let we ← ops.field s l
      ops.c0 we

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_push]:
    Source: 'lib.rs', lines 754:0-754:164 -/
def verifier.owned_push
  {D : Type} (ops : ClaimDotOps D)
  (dot : D) (g : Array aspis_core.field.WideExact 29#usize)
  (l : Std.Usize) (scalar : aspis_core.field.QM31) :
  Result ((core.result.Result Unit Unit) × D)
  := do
  let we ← Array.index_usize g l
  ops.pushDot dot we scalar

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_sum]: loop body 0:
    Source: 'lib.rs', lines 756:8-756:95 -/
@[rust_loop_body]
def verifier.owned_sum_loop.body
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize)
  (iter : core.ops.range.Range Std.Usize) (claim : aspis_core.field.WideExact)
  :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.field.WideExact) aspis_core.field.WideExact)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done claim)
  | some i =>
    let we ← Array.index_usize parts i
    trace.value 14#u16 i we
    let we1 ← Array.index_usize k i
    let we2 ← aspis_core.field.WideExact.mul we1 we
    let claim1 ← aspis_core.field.WideExact.add claim we2
    ok (cont (iter1, claim1))

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_sum]: loop 0:
    Source: 'lib.rs', lines 756:8-756:95 -/
@[rust_loop]
def verifier.owned_sum_loop
  (iter : core.ops.range.Range Std.Usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize)
  (claim : aspis_core.field.WideExact) :
  Result aspis_core.field.WideExact
  := do
  loop
    (fun (iter1, claim1) => verifier.owned_sum_loop.body k parts iter1 claim1)
    (iter, claim)

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_sum]:
    Source: 'lib.rs', lines 755:0-758:15 -/
def verifier.owned_sum
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result aspis_core.field.WideExact
  := do
  let claim ←
    verifier.owned_sum_loop { start := 0#usize, «end» := 7#usize } k parts
      aspis_core.field.WideExact.ZERO
  trace.value 14#u16 7#usize claim
  ok claim

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_claim_loops]: loop body 1:
    Source: 'lib.rs', lines 764:12-771:1 -/
@[rust_loop_body]
def verifier.owned_claim_loops_loop0_loop0.body
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (g : Array aspis_core.field.WideExact 29#usize)
  (point : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (dot : D) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    D) (D × (Option (core.result.Result
    aspis_core.field.WideExact verifier.Error))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (dot, none))
  | some l =>
    let scalar ← verifier.owned_scalar ops claims extra before_z1 y1 point l
    let (r, next) ← verifier.owned_push ops dot g l scalar
    let b ← ownedIsErr r
    if b
    then ok (done (next, some (core.result.Result.Err verifier.Error.Parse)))
    else ok (cont (iter1, next))

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_claim_loops]: loop 1:
    Source: 'lib.rs', lines 764:12-771:1 -/
@[rust_loop]
def verifier.owned_claim_loops_loop0_loop0
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (iter : core.ops.range.Range Std.Usize)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (g : Array aspis_core.field.WideExact 29#usize)
  (point : Std.Usize) (dot : D) :
  Result (D × (Option (core.result.Result
    aspis_core.field.WideExact verifier.Error)))
  := do
  loop
    (fun (iter1, dot1) => verifier.owned_claim_loops_loop0_loop0.body ops claims
      extra before_z1 y1 g point iter1 dot1)
    (iter, dot)

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_claim_loops]: loop body 0:
    Source: 'lib.rs', lines 762:8-771:1 -/
@[rust_loop_body]
def verifier.owned_claim_loops_loop0.body
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (g : Array aspis_core.field.WideExact 29#usize)
  (iter : core.ops.range.Range Std.Usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.WideExact 7#usize)) ((Array aspis_core.field.WideExact
    7#usize) × (Option (core.result.Result aspis_core.field.WideExact
    verifier.Error))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (parts, none))
  | some point =>
    let dot ← ops.newDot
    let (dot1, pending_return) ←
      verifier.owned_claim_loops_loop0_loop0 ops
        { start := 0#usize, «end» := 29#usize } claims extra before_z1 y1 g
        point dot
    match pending_return with
    | none =>
      let we ← ops.finishDot dot1
      let i ← point + 1#usize
      let parts1 ← Array.update parts i we
      ok (cont (iter1, parts1))
    | some _ => ok (done (parts, pending_return))

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_claim_loops]: loop 0:
    Source: 'lib.rs', lines 762:8-771:1 -/
@[rust_loop]
def verifier.owned_claim_loops_loop0
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (iter : core.ops.range.Range Std.Usize)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (g : Array aspis_core.field.WideExact 29#usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result ((Array aspis_core.field.WideExact 7#usize) × (Option
    (core.result.Result aspis_core.field.WideExact verifier.Error)))
  := do
  loop
    (fun (iter1, parts1) => verifier.owned_claim_loops_loop0.body ops claims extra
      before_z1 y1 g iter1 parts1)
    (iter, parts)

/-- [aspis_r1_verify_prepared_prefix::verifier::owned_claim_loops]:
    Source: 'lib.rs', lines 759:0-771:1 -/
def verifier.owned_claim_loops
  {D : Type} {N : Usize} (ops : ClaimDotOps D)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extra : Array aspis_core.field.QM31 29#usize)
  (before_z1 : Array aspis_core.field.QM31 29#usize)
  (y1 : Array Std.U8 N) (inactive : aspis_core.field.WideExact)
  (g : Array aspis_core.field.WideExact 29#usize)
  (kappa : aspis_core.field.WideExact) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  let k ← ops.powers 7#usize kappa
  let parts := Array.repeat 7#usize aspis_core.field.WideExact.ZERO
  let parts1 ← Array.update parts 0#usize inactive
  let (parts2, pending_return) ←
    verifier.owned_claim_loops_loop0 ops { start := 0#usize, «end» := 6#usize }
      claims extra before_z1 y1 g parts1
  match pending_return with
  | none =>
    let we ← verifier.owned_sum k parts2
    ok (core.result.Result.Ok we)
  | some r => ok r

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_owned]:
    Source: 'lib.rs', lines 772:0-772:271
    Visibility: public -/
def verifier.prepared_claim_owned
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Array Std.U8 928#usize)
  (inactive : aspis_core.field.WideExact)
  (g : Array aspis_core.field.WideExact 29#usize)
  (kappa : aspis_core.field.WideExact) :
  Result ((core.result.Result aspis_core.field.WideExact verifier.Error) ×
    (r1_semantic.Verified H))
  := do
  let result ←
    verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g
      kappa
  ok (result, sem)

end AspisR1CurrentPreparedClaim
