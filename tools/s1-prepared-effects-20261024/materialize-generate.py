#!/usr/bin/env python3
"""Outline the exact source query prefix, retaining ALL source operations."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
p=S/'S1PreparedQueryEffectsV1.lean';raw=p.read_text();a=raw.index('  let a := Array.repeat 32#usize');b=raw.index('  let r ← B.decode',a);c=raw.index('\nprivate theorem bind_congr',b)
prefix=raw[a:b];suffix=raw[b:c].rstrip()
header='''import S1PreparedQueryEffectsV1
import S1PreparedCodeLawsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result ControlFlow
universe v
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks8 := Array Bytes32 8#usize

def materialize {M : Type → Type v} [Monad M] [MonadLiftT Result M]
    (effects : PreparedHashEffects.Effects M) {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (hash : H) (state0 : Bytes32) : M (Blocks8 × Blocks8) := do
'''
mid='''
  pure (blocks15,blocks16)

def finish {M : Type → Type v} [Monad M] [MonadLiftT Result M]
    (B : QueriesModel.Boundaries) {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (self1 : transcript.Transcript H) (blocks15 blocks16 : Blocks8) :
    M (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
'''
footer='''

def queriesFactored {M : Type → Type v} [Monad M] [MonadLiftT Result M]
    (effects : PreparedHashEffects.Effects M) (B : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    M (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
  let absorbed ← PreparedHashEffects.absorb effects D self row payload
  let (blocks,advances) ← materialize effects D absorbed.hash absorbed.state
  finish B D absorbed blocks advances

private theorem code_bind_congr {A B : Type} (p : PreparedHashCode.Code A)
    (f g : A → PreparedHashCode.Code B) (h : ∀ a, f a=g a) : (p >>= f)=(p >>= g) :=
  congrArg (fun next => p >>= next) (funext h)

/-- Equality of complete typed code, not Result erasure. All sixteen source
calls, array updates, index operations, errors and continuation are retained. -/
theorem code_eq_factored (B : QueriesModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    PreparedQueryEffects.queries PreparedHashCode.effects B D self row payload=
      queriesFactored PreparedHashCode.effects B D self row payload := by
  unfold PreparedQueryEffects.queries queriesFactored materialize finish
  repeat' first
    | (with_reducible apply code_bind_congr; intro x)
    | (conv => rhs; rw [PreparedHashCode.code_bind_assoc])
    | rfl
    | split

#print axioms code_eq_factored
end AspisR1PublicPreparation.PreparedQueryMaterialize
'''
out=header+prefix.replace('self1.hash','hash').replace('self1.state','state0')+mid+suffix+footer
target=S/'S1QueryMaterializeEffectsV1.lean';mp=E/'s1-query-materialize-effects-source-pins.json';sha=lambda s:hashlib.sha256(s.encode()).hexdigest();meta=dict(schema='focused-extractor-proof-packet-v1',source=str(p.relative_to(R)),source_sha256=sha(raw),prefix_sha256=sha(prefix),suffix_sha256=sha(suffix),candidate_sha256=sha(out),digest_calls=prefix.count('effects.digest'),transformation='Exact source prefix/suffix outlining. Prefix alone substitutes self1.hash/state projections by explicit parameters; returns complete source arrays. No deletion/reordering of operations. Full Code equality must kernel-check.')
assert meta['digest_calls']==16
if '--check' in sys.argv:assert target.read_text()==out and json.loads(mp.read_text())==meta
else:target.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(digest_calls=16,source_operations_retained=True)))
