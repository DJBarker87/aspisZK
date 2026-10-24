#!/usr/bin/env python3
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
p=S/'S1QueryMaterializeEffectsV1.lean';raw=p.read_text();a=raw.index('  let a := Array.repeat 32#usize');b=raw.index('\ndef finish ',a);src=raw[a:b].rstrip()
pat=r'  let (s\d*) ← lift \(Array.to_slice (state\d*)\)\n  let (s\d*) ← lift \(Array.to_slice \(Array.make 1#usize \[ ([12])#u8 \]\)\)\n  let (s\d*) ← lift \(Array.to_slice \(Array.make 2#usize \[ \1, \3 \]\)\)\n  let (a\d+) ← effects.digest aspis_coreDigest32Inst hash \5'
body,count=re.subn(pat,lambda m:f'  let {m[6]} ← QueryPair.readState aspis_coreDigest32Inst hash {m[2]} {m[4]}#u8',src)
assert count==16,(count,src[:900])
header='''import S1QueryMaterializeEffectsV1
import S1PreparedCodeProductLawsV1
import S1QueryReadPairProgramV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode

def materializeReads {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (hash : H) (state0 : Bytes32) : Code (Blocks8 × Blocks8) := do
'''
compact='''

def materializePairs {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state0 : Bytes32) : Code (Blocks8 × Blocks8) := do
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let a1 ← QueryPair.readState D hash state0 1#u8
  let (_,back) ← Array.index_mut_usize blocks 0#usize
  let a2 ← QueryPair.readState D hash state0 2#u8
  let advances := back a2
  let state ← Array.index_usize advances 0#usize
  let (state1,blocks3,blocks4) ← QueryPair.pairStep D hash state (back a1) advances 1#usize
'''
for i in range(2,8):
 state=f'state{i}' if i<7 else '_'
 compact+=f'  let ({state},blocks{2*i+1},blocks{2*i+2}) ← QueryPair.pairStep D hash state{i-1} blocks{2*i-1} blocks{2*i} {i}#usize\n'
compact+='  pure (blocks15,blocks16)\n'
footer='''
private theorem code_bind_congr {A B : Type} (p : Code A) (f g : A → Code B)
    (h : ∀ a, f a=g a) : (p >>= f)=(p >>= g) :=
  congrArg (fun next => p >>= next) (funext h)

theorem materialize_code_eq_reads {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state : Bytes32) :
    materialize effects D hash state=materializeReads D hash state := by
  unfold materialize materializeReads QueryPair.readState
  repeat' first
    | (fail_if_no_progress (injections; subst_vars))
    | (with_reducible apply code_pair_bind_congr; intro a b)
    | (with_reducible apply code_bind_congr; intro x)
    | (conv => rhs; rw [code_left_unit])
    | (conv => rhs; rw [code_bind_assoc])
    | (with_reducible rfl)
    | split

theorem materialize_code_eq_pairs {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state : Bytes32) :
    materialize effects D hash state=materializePairs D hash state := by
  rw [materialize_code_eq_reads]
  unfold materializeReads materializePairs QueryPair.pairStep
  repeat' first
    | (fail_if_no_progress (injections; subst_vars))
    | (with_reducible apply code_pair_bind_congr; intro a b)
    | (with_reducible apply code_bind_congr; intro x)
    | (conv => rhs; rw [code_left_unit])
    | (conv => rhs; rw [code_bind_assoc])
    | (with_reducible rfl)
    | split

#print axioms materialize_code_eq_reads
#print axioms materialize_code_eq_pairs
end AspisR1PublicPreparation.PreparedQueryMaterialize
'''
out=header+body+compact+footer;target=S/'S1QueryMaterializePairsV1.lean';mp=E/'s1-query-materialize-pairs-source-pins.json';sha=lambda s:hashlib.sha256(s.encode()).hexdigest();meta=dict(schema='focused-extractor-proof-packet-v1',source=str(p.relative_to(R)),source_sha256=sha(raw),span_sha256=sha(src),candidate_sha256=sha(out),outlined_source_read_groups=count,transformation='All sixteen exact source read argument-construction groups outlined into readState; identical source array operations retained. Seven later source pairs outlined into pairStep. First source index_mut/back ownership flow retained. Full Code equality required, not value erasure.')
if '--check' in sys.argv:assert target.read_text()==out and json.loads(mp.read_text())==meta
else:target.write_text(out);mp.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(outlined_source_read_groups=count)))
