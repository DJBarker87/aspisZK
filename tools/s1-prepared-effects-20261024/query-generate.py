#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';p=B/'lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean';raw=p.read_text();start=raw.index('def QueriesModel.queries ');end=raw.index('\ndef QueriesModel.entry ',start);src=raw[start:end].strip();body=src.replace('def QueriesModel.queries (B :', 'def queries {M : Type → Type v} [Monad M] [MonadLiftT Result M]\n    (effects : PreparedHashEffects.Effects M) (B :',1);body=re.sub(r'\n  Result ','\n  M ',body,count=1);body=body.replace('transcript.Transcript.absorb aspis_coreDigest32Inst','PreparedHashEffects.absorb effects aspis_coreDigest32Inst');body=body.replace('aspis_coreDigest32Inst.digest','effects.digest aspis_coreDigest32Inst');body=re.sub(r'\bok\b','pure',body)
assert src.count('aspis_coreDigest32Inst.digest')==16
header='''import S1PreparedScalarEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryEffects
open Aeneas Aeneas.Std Result ControlFlow
universe v
'''
footer='''
private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- All sixteen materialized read/advance calls are retained, even when the
scanner later chooses an earlier state or rejects. Full Result/self equality. -/
theorem queries_source (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    queries PreparedHashEffects.sourceEffects B D self row payload=
      QueriesModel.queries B D self row payload := by
  unfold queries QueriesModel.queries
  rw [PreparedHashEffects.absorb_source]
  repeat' first
    | (apply bind_congr; intro x)
    | rfl
    | split

#print axioms queries_source
end AspisR1PublicPreparation.PreparedQueryEffects
'''
out=header+body+'\n'+footer;target=S/'S1PreparedQueryEffectsV1.lean';meta=dict(schema='focused-extractor-proof-packet-v1',source=str(p.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),span_sha256=hashlib.sha256(src.encode()).hexdigest(),candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),digest_calls_retained=16,transformation='Exact complete query source body, changing only name, monad/pure and explicit hash effects/absorb helper. No resource-option headers copied. Source array writes, all 16 reads, decode/embed/trace children, error and returned selected state retained.')
mp=E/'s1-prepared-query-effects-materialization.json'
if '--check' in sys.argv:assert target.read_text()==out and json.loads(mp.read_text())==meta
else:target.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(digest_calls_retained=16,full_source=True)))
