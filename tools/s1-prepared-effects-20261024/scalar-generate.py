#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';p=B/'lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/ExtractedPreparedModel.lean';raw=p.read_text();chunks=[];spans={}
for name,nextname in [('scalar','scalar_k'),('scalar_k','prepare')]:
 start=raw.index('def PreparedModel.'+name+' ');end=raw.index('def PreparedModel.'+nextname+' ',start);src=raw[start:end].strip();body=src.replace('def PreparedModel.'+name+' (B :', 'def '+name+' {M : Type → Type v} [Monad M] [MonadLiftT Result M]\n    (effects : PreparedHashEffects.Effects M) (B :',1);body=re.sub(r'\n  Result ','\n  M ',body,count=1);body=body.replace('transcript.Transcript.block aspis_coreDigest32Inst','PreparedHashEffects.block effects aspis_coreDigest32Inst');body=re.sub(r'\bok\b','pure',body);chunks.append(body);spans[name]=hashlib.sha256(src.encode()).hexdigest()
header='''import S1PreparedHashErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedScalarEffects
open Aeneas Aeneas.Std Result
universe v
'''
footer='''
theorem scalar_source (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
    scalar PreparedHashEffects.sourceEffects B D self row payload nonzero=
      PreparedModel.scalar B D self row payload nonzero := by cases nonzero <;> rfl

theorem scalar_k_source (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    scalar_k PreparedHashEffects.sourceEffects B D self row payload=
      PreparedModel.scalar_k B D self row payload := rfl

#print axioms scalar_source
#print axioms scalar_k_source
end AspisR1PublicPreparation.PreparedScalarEffects
'''
out=header+'\n\n'.join(chunks)+'\n'+footer;target=S/'S1PreparedScalarEffectsV1.lean';meta=dict(schema='focused-extractor-proof-packet-v1',source=str(p.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),spans=spans,candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),transformation='Exact source scalar/scalar_k bodies; only hash-block child effects, function names, monad and pure generalized. Sampler/fromQm/trace Result children retain original calls and errors.')
mp=E/'s1-prepared-scalar-effects-materialization.json'
if '--check' in sys.argv:assert target.read_text()==out and json.loads(mp.read_text())==meta
else:target.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
