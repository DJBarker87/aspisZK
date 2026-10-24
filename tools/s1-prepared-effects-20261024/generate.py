#!/usr/bin/env python3
"""Lift the exact retained original Prepared::new body, not a replacement model."""
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
raw=(S/'CurrentOriginalPreparedNativeV1.lean').read_text();start=raw.index('def OriginalPreparedNative.prepare ');end=raw.index('/-- Complete Result',start);body=raw[start:end].strip()
body=body.replace('def OriginalPreparedNative.prepare (B : PreparedScratchModel.Boundaries)', 'def prepare {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)')
body=body.replace('  Result ((core.result.Result verifier.Prepared verifier.Error)', '  M ((core.result.Result verifier.Prepared verifier.Error)',1)
changes={'transcript.Transcript.new':'effects.newTranscript','PreparedModel.scalar B.sampling':'effects.scalar','B.sampling.toBytes':'effects.toBytes','B.sampling.queries':'effects.queries','PreparedModel.scalar_k B.sampling':'effects.rho','B.powers':'effects.powers','B.claim':'effects.claim'}
for old,new in changes.items():assert old in body,old;body=body.replace(old,new)
body=re.sub(r'\bok\b','pure',body)
header='''import CurrentOriginalPreparedNativeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedSourceEffects
open Aeneas Aeneas.Std Result ControlFlow
universe v

/-- Source child calls retain complete original types and all arguments.
These effects are not concrete source-oracle or mathematical model ports. -/
structure Effects (M : Type → Type v) where
  newTranscript : {H : Type} → aspis_core.Digest32 H → H → Array U8 32#usize → transport.Variant → M (transcript.Transcript H)
  scalar : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → Bool → M (aspis_core.field.WideExact × transcript.Transcript H)
  toBytes : aspis_core.field.WideExact → M (Array U8 32#usize)
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → M (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  rho : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → M (aspis_core.field.QM31 × transcript.Transcript H)
  powers : (N : Usize) → aspis_core.field.WideExact → M (Array aspis_core.field.WideExact N)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 → aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize → aspis_core.field.WideExact → M (core.result.Result aspis_core.field.WideExact verifier.Error)

def sourceEffects (B : PreparedScratchModel.Boundaries) : Effects Result where
  newTranscript := transcript.Transcript.new
  scalar := PreparedModel.scalar B.sampling
  toBytes := B.sampling.toBytes
  queries := B.sampling.queries
  rho := PreparedModel.scalar_k B.sampling
  powers := B.powers
  claim := B.claim

'''
footer='''
/-- Full Result and returned scratch, including query rejection before scratch
replacement and claim rejection afterwards. No accepted-run hypothesis. -/
theorem source_exact (B : PreparedScratchModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (view : verifier.View)
    (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) :
    prepare (sourceEffects B) D sem view hash scratch =
      OriginalPreparedNative.prepare B D sem view hash scratch := rfl

#print axioms source_exact
end AspisR1PublicPreparation.PreparedSourceEffects
'''
out=header+body+'\n'+footer;p=S/'S1PreparedSourceEffectsV1.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
meta=dict(schema='focused-extractor-proof-packet-v1',source='CurrentOriginalPreparedNativeV1.lean',source_sha256=sha(raw),span_sha256=sha(raw[start:end]),candidate_sha256=sha(out),transformation='Exact emitted body, Result generalized to M, seven child calls parameterized, ok generalized to pure. Original carriers, branches, error constructors and scratch returns retained. source_exact must kernel-check; effect interpretation/model order is not asserted.')
p=E/'s1-prepared-source-effects-materialization.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(exact_source_body=True,concrete_oracle_join=False)))
