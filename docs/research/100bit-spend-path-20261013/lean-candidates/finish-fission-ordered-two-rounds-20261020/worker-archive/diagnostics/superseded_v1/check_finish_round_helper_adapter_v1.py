#!/usr/bin/env python3
"""Mechanical source/adapter correspondence inventory (not a semantic proof)."""
from pathlib import Path
import hashlib, json
RUST=Path('/tmp/finish-round-alpha-candidate-v1/input/lib.rs')
FUNS=Path('/tmp/FinishRoundHelperOpaqueSelectors-Funs.lean')
ADAPTER=Path('/tmp/FinishFissionHelperAdapterV1.lean')
OPS=Path('docs/research/100bit-spend-path-20261013/lean-candidates/finish-relation-source-candidate-20261019/sources/FinishCandidateExplicitOps.lean')
def sha(b): return hashlib.sha256(b).hexdigest()
def rust_def(text,name):
    key=f'pub fn {name}('
    start=text.index(key); op=text.index('{',start); depth=0
    for i in range(op,len(text)):
        if text[i]=='{': depth+=1
        elif text[i]=='}':
            depth-=1
            if depth==0: return start,i+1,text[start:i+1]
    raise AssertionError('unterminated Rust function '+name)
def lean_def(text,name,next_marker='\nend AspisR1FinishRelationCurrent'):
    start=text.index('def '+name); end=text.index(next_marker,start)
    return text[start:end]
rust_bytes=RUST.read_bytes(); rt=rust_bytes.decode(); rs,re,rb=rust_def(rt,'finish_relation_round')
assert sha(rust_bytes)=='a222c9f1a4da189e5123e324a6586c95d31b10cf63fb1cba61686c0a6928b6f8'
assert sha(rb.encode())=='e664741d2208bac1355c5b53e8f367dc50c7d70e08ffc6ca4e7bf27a629ca943'
rust_order=['select_round_poly(v,round)','field(poly,0)','field(poly,4)','field(poly,0).add(field(poly,4))','claim.mul_m31(QUARTER)','crate::trace::value(15,3*round,lhs)','crate::trace::value(15,3*round+1,rhs)','iflhs!=rhs','polynomial(poly,p.alpha[round])','crate::trace::value(15,3*round+2,claim)','Ok(claim)']
rnorm=''.join(rb.split())
for token in rust_order: assert token in rnorm, token
ft=FUNS.read_text(); fb=lean_def(ft,'verifier.finish_relation_round')
lean_order=['verifier.select_round_poly v round','weights.field poly 0#usize','weights.field poly 4#usize','aspis_core.field.WideExact.add we we1','weights.QUARTER','aspis_core.field.WideExact.mul_m31 claim m','trace.value 15#u16 i lhs','trace.value 15#u16 i1 rhs','core.cmp.PartialEq.ne.trait_default','if b','Array.index_usize p.alpha round','verifier.polynomial poly we2','trace.value 15#u16 i2 claim1']
pos=-1
for token in lean_order:
    n=fb.find(token,pos+1); assert n>=0, token; pos=n
at=ADAPTER.read_text(); adapter=at[at.index('def finishRoundAdapter '):at.index('\nprivate theorem bind_success')]
assert 'selectRoundPolyModel v round' in adapter
assert 'selectRoundAlphaModel p round' in adapter
assert 'verifier.finish_relation_round ops poly alpha claim round' in adapter
ot=OPS.read_text(); ob=lean_def(ot,'verifier.finish_relation_round','\n/-- [aspis_r1_finish_relation_current::verifier::finish_query_dot')
ops_order=['ops.field poly 0#usize','ops.field poly 4#usize','ops.add we we1','ops.quarter','ops.mulM31 claim m','trace.value 15#u16 i lhs','trace.value 15#u16 i1 rhs','core.cmp.PartialEq.ne.trait_default','if b','ops.polynomial poly alpha','trace.value 15#u16 i2 claim1']
pos=-1
for token in ops_order:
    n=ob.find(token,pos+1); assert n>=0, token; pos=n
print(json.dumps({
 'classification':'structural mapping only; not a proof of external-operation refinement or production reachability',
 'rust_candidate_lib_sha256':sha(rust_bytes),'rust_function_span':[rs,re],'rust_helper_sha256':sha(rb.encode()),
 'generated_funs_sha256':sha(FUNS.read_bytes()),'generated_helper_sha256':sha(fb.encode()),
 'adapter_source_sha256':sha(ADAPTER.read_bytes()),'explicit_ops_source_sha256':sha(OPS.read_bytes()),
 'validated_call_order':['selected polynomial','field[0]','field[4]','add','QUARTER','mul_m31','trace lhs/rhs','inequality guard','selected alpha','polynomial evaluation','trace output'],
 'external_or_model_boundaries':['field lookup weights.field','WideExact.add','QUARTER','WideExact.mul_m31','PartialEq eq/ne semantics','polynomial evaluation','trace'],
 'status':'PASS'},indent=2))
