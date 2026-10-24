#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';p=B/'lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean';raw=p.read_text()
header='''import S1PreparedSourceEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashEffects
open Aeneas Aeneas.Std Result
universe v

structure Effects (M : Type → Type v) where
  digest : {H : Type} → aspis_core.Digest32 H → H → Slice (Slice U8) → M (Array U8 32#usize)

def sourceEffects : Effects Result where digest := fun D hash parts => D.digest hash parts

'''
chunks=[];pins={}
for name in ['new','absorb','block']:
 start=raw.index('def transcript.Transcript.'+name+'\n');end=raw.index('\n/--',start) if name!='block' else raw.index('\n\n\n/-! Exact newly',start);src=raw[start:end].strip()
 body=src.replace('def transcript.Transcript.'+name, 'def '+name+' {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)',1)
 body=re.sub(r'\n  Result ', '\n  M ',body,count=1)
 body=body.replace('aspis_coreDigest32Inst.digest','effects.digest aspis_coreDigest32Inst')
 body=body.replace('transcript.Transcript.absorb aspis_coreDigest32Inst','absorb effects aspis_coreDigest32Inst')
 body=re.sub(r'\bok\b','pure',body);chunks.append(body);pins[name]=hashlib.sha256(src.encode()).hexdigest()
footer='''
theorem new_source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Array U8 32#usize) (variant : transport.Variant) :
    new sourceEffects D hash state variant=transcript.Transcript.new D hash state variant := rfl

theorem absorb_source {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    absorb sourceEffects D self row payload=transcript.Transcript.absorb D self row payload := rfl

theorem block_source {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    block sourceEffects D self row payload=transcript.Transcript.block D self row payload := rfl

#print axioms new_source
#print axioms absorb_source
#print axioms block_source
end AspisR1PublicPreparation.PreparedHashEffects
'''
out=header+'\n\n'.join(chunks)+'\n'+footer;target=S/'S1PreparedHashEffectsV1.lean';meta=dict(schema='focused-extractor-proof-packet-v1',source=str(p.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),spans=pins,candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),transformation='Only source function names, Result-to-M, ok-to-pure and explicit digest effect parameterization. Complete grouping, domain, cast/add errors, state and hash retained.')
mp=E/'s1-prepared-hash-effects-materialization.json'
if '--check' in sys.argv:assert target.read_text()==out and json.loads(mp.read_text())==meta
else:target.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(source_hash_helpers=3,oracle_model_join=False)))
