#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';O=B/'lean-candidates/s126-caller-boundary-20261021';raw=(B/'evidence/s126-current-caller-20261021/host/prepared-v7/generated/AspisR1CurrentCaller/Funs.lean.txt').read_text();a=raw.index('def verifier.Prepared.new\n');b=raw.index('\n/--',a);raw=raw[a:b]
header='''import CurrentOriginalPreparedNativeV1
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
'''
mapping={'verifier.Prepared.new':'prepare B','transcript.Transcript.scalar_k':'scalarK B','transcript.Transcript.scalar':'scalar B','transcript.Transcript.queries':'queries B','transcript.Transcript.new':'newT','transcript.Transcript':'Transcript','r1_wire.SemanticTranscript.impl.state':'semanticState','aspis_core.field.wide_exact.WideExact.to_le_bytes':'toBytes B','aspis_core.field.wide_exact.WideExact.ZERO':'zero','transport.Variant.folds':'folds','weights.powers':'powers B','verifier.prepared_claim':'claim B'}
pat=re.compile(r'(?<![A-Za-z0-9_.])(?:'+'|'.join(re.escape(n) for n in sorted(mapping,key=len,reverse=True))+r')(?![A-Za-z0-9_.])');body=pat.sub(lambda m:mapping[m[0]],raw).replace('def prepare B\n','def prepare (B : Boundaries)\n',1)
tail='''
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
'''
start=tail.index('  unfold prepare transported AspisR1PublicPreparation.OriginalPreparedNative.prepare\n');end=tail.index('\n#print axioms prepare',start)
tail=tail[:start]+Path(__file__).with_name('carrier-transport-proof.lean.inc').read_text()+tail[end:]
(O/'CurrentOriginalPreparedCarrierTransportV1.lean').write_text(header+body+tail)
(O/'original-prepared-carrier-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_body_sha256=hashlib.sha256(raw.encode()).hexdigest(),identifier_map=mapping,added_binder='B : Boundaries',qualification='Fresh original body under all complete concrete current carriers. Primitive children are coordinate-preserving interpretations; their actual installation must be justified separately.'),indent=2)+'\n')
