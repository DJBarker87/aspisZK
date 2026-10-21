import CurrentOriginalPreparedNativeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentCaller.OriginalPreparedSource
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
/-- Complete freshly emitted transcript carrier: both original fields. -/
structure Transcript (H : Type) where
  state : Array U8 32#usize
  hash : H

def retainedT {H : Type} (x : Transcript H) : AspisR1PublicPreparation.transcript.Transcript H :=
  {state:=x.state,hash:=x.hash}
def currentT {H : Type} (x : AspisR1PublicPreparation.transcript.Transcript H) : Transcript H :=
  {state:=x.state,hash:=x.hash}
@[simp] theorem t_round {H : Type} (x : AspisR1PublicPreparation.transcript.Transcript H) : retainedT (currentT x)=x := rfl
@[simp] theorem q_round (x : AspisR1PublicPreparation.aspis_core.field.QM31) : retainedQ (currentQ x)=x := rfl
@[simp] theorem e_round (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : retainedE (currentE x)=x := rfl
@[simp] theorem q_round_current (x : aspis_core.field.QM31) : currentQ (retainedQ x)=x := rfl
@[simp] theorem point_round_current (x : aspis_core.circle.SecureCirclePoint) : currentPoint (retainedPoint x)=x := rfl
@[simp] theorem variant_round (x : transport.Variant) : currentVariant (retainedVariant x)=x := by cases x <;> rfl
@[simp] theorem e_round_current (x : aspis_core.field.wide_exact.WideExact) : currentE (retainedE x)=x := rfl
@[simp] theorem e_array_round_current {N : Usize} (x : Array aspis_core.field.wide_exact.WideExact N) :
    mapArray currentE (mapArray retainedE x)=x := mapArray_inverse retainedE currentE e_round_current x
@[simp] theorem e_array_round {N : Usize} (x : Array AspisR1PublicPreparation.aspis_core.field.WideExact N) :
    mapArray retainedE (mapArray currentE x)=x := mapArray_inverse currentE retainedE e_round x
@[simp] theorem q_array_round_current {N : Usize} (x : Array aspis_core.field.QM31 N) :
    mapArray currentQ (mapArray retainedQ x)=x := mapArray_inverse retainedQ currentQ q_round_current x
@[simp] theorem point_array_round_current {N : Usize} (x : Array aspis_core.circle.SecureCirclePoint N) :
    mapArray currentPoint (mapArray retainedPoint x)=x := mapArray_inverse retainedPoint currentPoint point_round_current x

def currentR {A : Type} (f : A → aspis_core.field.wide_exact.WideExact)
    (x : core.result.Result A AspisR1PublicPreparation.verifier.Error) :
    core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error :=
  match x with | .Ok a => .Ok (f a) | .Err e => .Err (currentError e)

abbrev Boundaries := AspisR1PublicPreparation.PreparedScratchModel.Boundaries

def semanticState {H : Type} (D : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) :=
  AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state (retainedDigest D)
    {state:=t.state,hash:=t.hash,next_row:=t.next_row}
def newT {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (state : Array U8 32#usize) (v : transport.Variant) : Result (Transcript H) := do
  let t ← AspisR1PublicPreparation.transcript.Transcript.new (retainedDigest D) hash state (retainedVariant v)
  ok (currentT t)
def scalar (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H) (t : Transcript H) (row : U8) (bytes : Slice U8) (nz : Bool) : Result (aspis_core.field.wide_exact.WideExact × Transcript H) := do
  let (a,t) ← AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) (retainedT t) row bytes nz
  ok (currentE a,currentT t)
def toBytes (B : Boundaries) (x : aspis_core.field.wide_exact.WideExact) := B.sampling.toBytes (retainedE x)
def folds (v : transport.Variant) := AspisR1PublicPreparation.transport.Variant.folds (retainedVariant v)
def queries (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H) (t : Transcript H) (row : U8) (bytes : Slice U8) :
    Result (core.result.Result (Array U32 22#usize) verifier.Error × Transcript H) := do
  let (a,t) ← B.sampling.queries (retainedDigest D) (retainedT t) row bytes
  ok ((match a with | .Ok x => .Ok x | .Err e => .Err (currentError e)),currentT t)
def scalarK (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H) (t : Transcript H) (row : U8) (bytes : Slice U8) : Result (aspis_core.field.QM31 × Transcript H) := do
  let (a,t) ← AspisR1PublicPreparation.PreparedModel.scalar_k B.sampling (retainedDigest D) (retainedT t) row bytes
  ok (currentQ a,currentT t)
def powers (B : Boundaries) (N : Usize) (x : aspis_core.field.wide_exact.WideExact) : Result (Array aspis_core.field.wide_exact.WideExact N) := do
  let g ← B.powers N (retainedE x)
  ok (mapArray currentE g)
def claim (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (kappa : aspis_core.field.wide_exact.WideExact) : Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error) := do
  let r ← B.claim (retainedDigest D) (retainedSem sem) y1 (retainedE inactive) (mapArray retainedE g) (retainedE kappa)
  ok (currentR currentE r)
def zero : Result aspis_core.field.wide_exact.WideExact := ok (currentE AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO)
def prepare (B : Boundaries)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
  := do
  let a ←
    semanticState aspis_coredigestDigest32Inst
      sem.transcript
  let t ←
    newT aspis_coredigestDigest32Inst hash a v.variant
  let (gamma, t1) ←
    scalar B aspis_coredigestDigest32Inst t 27#u8 v.y1 true
  let a1 ← toBytes B v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    scalar B aspis_coredigestDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    scalar B aspis_coredigestDigest32Inst t2 29#u8 
      v.round0 false
  let i ← folds v.variant
  if i = 2#usize
  then
    let i1 ← 32#usize + 224#usize
    let bytes := alloc.vec.Vec.with_capacity Std.U8 i1
    let a2 ← core.option.Option.unwrap v.folded_root
    let s1 ← lift (Array.to_slice a2)
    let bytes1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes s1
    let bytes2 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1
    let s2 := alloc.vec.Vec.deref bytes2
    let (we, t4) ←
      scalar B aspis_coredigestDigest32Inst t3 30#u8 s2
        false
    let (r, t5) ←
      queries B aspis_coredigestDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        scalarK B aspis_coredigestDigest32Inst t5 i2 s3
      let g1 ← powers B 29#usize gamma
      let r1 ←
        claim B aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok
          {
            variant := v.variant,
            roots := sem.roots,
            gamma,
            kappa,
            alpha := (Array.make 2#usize [ alpha0, we ]),
            rho,
            queries := val,
            semantic_alpha := sem.alpha,
            z := sem.z,
            claim := val1,
            state := t6.state
          }, g1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (core.convert.FromSame verifier.Error) residual
        ok (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (r1, g)
  else
    let we ← zero
    let (r, t4) ←
      queries B aspis_coredigestDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        scalarK B aspis_coredigestDigest32Inst t4 i1 s1
      let g1 ← powers B 29#usize gamma
      let r1 ←
        claim B aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok
          {
            variant := v.variant,
            roots := sem.roots,
            gamma,
            kappa,
            alpha := (Array.make 2#usize [ alpha0, we ]),
            rho,
            queries := val,
            semantic_alpha := sem.alpha,
            z := sem.z,
            claim := val1,
            state := t5.state
          }, g1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (core.convert.FromSame verifier.Error) residual
        ok (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (r1, g)

private theorem bind_congr_same {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ x,f x=g x) : (do let x ← m;f x)=(do let x ← m;g x) := by
  have he : f=g := funext h
  rw [he]
private theorem pair_map {A B C D : Type} (p : A × B) (f : A → C) (g : B → D) :
    (let (a,b):=p; (ok (f a,g b) : Result (C × D)))=ok (f p.1,g p.2) := by cases p; rfl

def transported (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result verifier.Prepared verifier.Error) × Array aspis_core.field.wide_exact.WideExact 29#usize) := do
  let (r,g) ← AspisR1PublicPreparation.OriginalPreparedNative.prepare B (retainedDigest D)
    (retainedSem sem) (retainedView v) hash (mapArray retainedE g)
  ok ((match r with | .Ok x => .Ok (currentPrepared x) | .Err e => .Err (currentError e)),mapArray currentE g)

/-- Complete carrier transport, retaining all original fields and errors. -/
theorem prepare_transport (B : Boundaries) {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    prepare B D sem v hash g=transported B D sem v hash g := by
  unfold prepare transported AspisR1PublicPreparation.OriginalPreparedNative.prepare
  simp only [semanticState,newT,scalar,toBytes,folds,queries,scalarK,powers,claim,zero,
    AspisR1PublicPreparation.OriginalPreparedNative.zero,retainedView]
  cases h1 : AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state (retainedDigest D) (retainedSem sem).transcript with
  | fail e =>
    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h1
    try simp only [h1,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
    try rfl
  | div =>
    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h1
    try simp only [h1,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
    try rfl
  | ok seed =>
    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h1
    try simp only [h1,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
    cases h2 : AspisR1PublicPreparation.transcript.Transcript.new (retainedDigest D) hash seed (retainedVariant v.variant) with
    | fail e =>
      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h2
      try simp only [h2,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
      try rfl
    | div =>
      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h2
      try simp only [h2,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
      try rfl
    | ok t =>
      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h2
      try simp only [h2,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
      cases h3 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t 27#u8 v.y1 true with
      | fail e =>
        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h3
        try simp only [h3,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
        try rfl
      | div =>
        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h3
        try simp only [h3,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
        try rfl
      | ok value =>
        rcases value with ⟨gamma,t1⟩
        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h3
        try simp only [h3,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
        cases h4 : B.sampling.toBytes (retainedE v.inactive) with
        | fail e =>
          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h4
          try simp only [h4,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
          try rfl
        | div =>
          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h4
          try simp only [h4,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
          try rfl
        | ok encoded =>
          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h4
          try simp only [h4,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
          cases h5 : lift (Array.to_slice encoded) with
          | fail e =>
            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h5
            try simp only [h5,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
            try rfl
          | div =>
            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h5
            try simp only [h5,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
            try rfl
          | ok bytes =>
            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h5
            try simp only [h5,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
            cases h6 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t1 28#u8 bytes false with
            | fail e =>
              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h6
              try simp only [h6,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
              try rfl
            | div =>
              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h6
              try simp only [h6,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
              try rfl
            | ok value =>
              rcases value with ⟨kappa,t2⟩
              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h6
              try simp only [h6,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
              cases h7 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t2 29#u8 v.round0 false with
              | fail e =>
                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h7
                try simp only [h7,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                try rfl
              | div =>
                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h7
                try simp only [h7,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                try rfl
              | ok value =>
                rcases value with ⟨alpha0,t3⟩
                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h7
                try simp only [h7,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                cases h8 : AspisR1PublicPreparation.transport.Variant.folds (retainedVariant v.variant) with
                | fail e =>
                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h8
                  try simp only [h8,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                  try rfl
                | div =>
                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h8
                  try simp only [h8,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                  try rfl
                | ok foldCount =>
                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h8
                  try simp only [h8,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                  by_cases hdouble : foldCount=2#usize
                  ·
                    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at hdouble
                    try simp only [hdouble,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                    cases h9 : (32#usize + 224#usize : Result Usize) with
                    | fail e =>
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h9
                      try simp only [h9,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      try rfl
                    | div =>
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h9
                      try simp only [h9,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      try rfl
                    | ok capacity =>
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h9
                      try simp only [h9,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      cases h10 : core.option.Option.unwrap v.folded_root with
                      | fail e =>
                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h10
                        try simp only [h10,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                        try rfl
                      | div =>
                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h10
                        try simp only [h10,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                        try rfl
                      | ok foldedRoot =>
                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h10
                        try simp only [h10,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                        cases h11 : lift (Array.to_slice foldedRoot) with
                        | fail e =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h11
                          try simp only [h11,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          try rfl
                        | div =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h11
                          try simp only [h11,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          try rfl
                        | ok foldedBytes =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h11
                          try simp only [h11,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          cases h12 : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) foldedBytes with
                          | fail e =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h12
                            try simp only [h12,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            try rfl
                          | div =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h12
                            try simp only [h12,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            try rfl
                          | ok bytes1 =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h12
                            try simp only [h12,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            cases h13 : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1 with
                            | fail e =>
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h13
                              try simp only [h13,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              try rfl
                            | div =>
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h13
                              try simp only [h13,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              try rfl
                            | ok bytes2 =>
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h13
                              try simp only [h13,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              cases h14 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t3 30#u8 (alloc.vec.Vec.deref bytes2) false with
                              | fail e =>
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h14
                                try simp only [h14,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                try rfl
                              | div =>
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h14
                                try simp only [h14,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                try rfl
                              | ok value =>
                                rcases value with ⟨alpha1,t4⟩
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h14
                                try simp only [h14,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                cases h15 : B.sampling.queries (retainedDigest D) t4 31#u8 v.final_message with
                                | fail e =>
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h15
                                  try simp only [h15,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  try rfl
                                | div =>
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h15
                                  try simp only [h15,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  try rfl
                                | ok value =>
                                  rcases value with ⟨queryResult,t5⟩
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h15
                                  try simp only [h15,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  cases queryResult with
                                  | Err e => simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl
                                  | Ok actualQueries =>
                                    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                    cases h16 : (31#u8 + 1#u8 : Result U8) with
                                    | fail e =>
                                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h16
                                      try simp only [h16,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                      try rfl
                                    | div =>
                                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h16
                                      try simp only [h16,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                      try rfl
                                    | ok nextRow =>
                                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h16
                                      try simp only [h16,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                      cases h17 : lift (Array.to_slice (Std.Array.empty U8)) with
                                      | fail e =>
                                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h17
                                        try simp only [h17,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                        try rfl
                                      | div =>
                                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h17
                                        try simp only [h17,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                        try rfl
                                      | ok emptyBytes =>
                                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h17
                                        try simp only [h17,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                        cases h18 : AspisR1PublicPreparation.PreparedModel.scalar_k B.sampling (retainedDigest D) t5 nextRow emptyBytes with
                                        | fail e =>
                                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h18
                                          try simp only [h18,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                          try rfl
                                        | div =>
                                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h18
                                          try simp only [h18,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                          try rfl
                                        | ok value =>
                                          rcases value with ⟨rho,t6⟩
                                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h18
                                          try simp only [h18,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                          cases h19 : B.powers 29#usize gamma with
                                          | fail e =>
                                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h19
                                            try simp only [h19,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                            try rfl
                                          | div =>
                                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h19
                                            try simp only [h19,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                            try rfl
                                          | ok scratchOld =>
                                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h19
                                            try simp only [h19,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                            cases h20 : B.claim (retainedDigest D) (retainedSem sem) v.y1 (retainedE v.inactive) scratchOld kappa with
                                            | fail e =>
                                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h20
                                              try simp only [h20,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                              try rfl
                                            | div =>
                                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h20
                                              try simp only [h20,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                              try rfl
                                            | ok claimResult =>
                                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h20
                                              try simp only [h20,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                              cases claimResult with
                                              | Err e => simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl
                                              | Ok actualClaim =>
                                                simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl
                  ·
                    try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at hdouble
                    try simp only [hdouble,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                    cases h21 : B.sampling.queries (retainedDigest D) t3 30#u8 v.final_message with
                    | fail e =>
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h21
                      try simp only [h21,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      try rfl
                    | div =>
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h21
                      try simp only [h21,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      try rfl
                    | ok value =>
                      rcases value with ⟨queryResult,t4⟩
                      try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h21
                      try simp only [h21,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                      cases queryResult with
                      | Err e => simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl
                      | Ok actualQueries =>
                        try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                        cases h22 : (30#u8 + 1#u8 : Result U8) with
                        | fail e =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h22
                          try simp only [h22,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          try rfl
                        | div =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h22
                          try simp only [h22,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          try rfl
                        | ok nextRow =>
                          try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h22
                          try simp only [h22,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                          cases h23 : lift (Array.to_slice (Std.Array.empty U8)) with
                          | fail e =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h23
                            try simp only [h23,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            try rfl
                          | div =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h23
                            try simp only [h23,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            try rfl
                          | ok emptyBytes =>
                            try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h23
                            try simp only [h23,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                            cases h24 : AspisR1PublicPreparation.PreparedModel.scalar_k B.sampling (retainedDigest D) t4 nextRow emptyBytes with
                            | fail e =>
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h24
                              try simp only [h24,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              try rfl
                            | div =>
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h24
                              try simp only [h24,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              try rfl
                            | ok value =>
                              rcases value with ⟨rho,t5⟩
                              try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h24
                              try simp only [h24,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                              cases h25 : B.powers 29#usize gamma with
                              | fail e =>
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h25
                                try simp only [h25,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                try rfl
                              | div =>
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h25
                                try simp only [h25,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                try rfl
                              | ok scratchOld =>
                                try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h25
                                try simp only [h25,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                cases h26 : B.claim (retainedDigest D) (retainedSem sem) v.y1 (retainedE v.inactive) scratchOld kappa with
                                | fail e =>
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h26
                                  try simp only [h26,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  try rfl
                                | div =>
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h26
                                  try simp only [h26,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  try rfl
                                | ok claimResult =>
                                  try simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] at h26
                                  try simp only [h26,Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray]
                                  cases claimResult with
                                  | Err e => simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl
                                  | Ok actualClaim =>
                                    simp only [Bind.bind,instBindResult,Aeneas.Std.bind,uncurry,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,q_array_round_current,point_array_round_current,variant_round,currentT,retainedT,retainedView,retainedSem,currentR,currentPrepared,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,mapArray] <;> try rfl

#print axioms prepare
#print axioms prepare_transport
end AspisR1CurrentCaller.OriginalPreparedSource
