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
  cases h0 : AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state (retainedDigest D) (retainedSem sem).transcript with
  | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
  | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
  | ok seed =>
    try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
    cases h1 : AspisR1PublicPreparation.transcript.Transcript.new (retainedDigest D) hash seed (retainedVariant v.variant) with
    | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
    | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
    | ok t =>
      try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
      cases h2 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t 27#u8 v.y1 true with
      | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
      | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
      | ok p =>
        rcases p with ⟨gamma,t1⟩
        try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
        cases h3 : B.sampling.toBytes (retainedE v.inactive) with
        | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
        | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
        | ok encoded =>
          try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
          cases h4 : lift (Array.to_slice encoded) with
          | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
          | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
          | ok bytes =>
            try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
            cases h5 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t1 28#u8 bytes false with
            | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
            | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
            | ok p =>
              rcases p with ⟨kappa,t2⟩
              try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
              cases h6 : AspisR1PublicPreparation.PreparedModel.scalar B.sampling (retainedDigest D) t2 29#u8 v.round0 false with
              | fail e => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
              | div => simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
              | ok p =>
                rcases p with ⟨alpha0,t3⟩
                try simp_all! only [Bind.bind,instBindResult,Aeneas.Std.bind,bind_tc_ok,bind_assoc_eq,t_round,e_round,e_array_round,e_array_round_current,currentT,retainedT,retainedView,retainedSem,currentR,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from] <;> try rfl
                trace_state
                fail "prefix normalization diagnostic"

#print axioms prepare
#print axioms prepare_transport
end AspisR1CurrentCaller.OriginalPreparedSource
