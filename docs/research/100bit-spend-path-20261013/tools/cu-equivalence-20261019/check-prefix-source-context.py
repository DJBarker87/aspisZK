#!/usr/bin/env python3
"""Inverse source factoring of the sole production fixed-prefix helper caller."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;repo=tool.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest();candidate='225a3736d8afb8e8d77b38f1b62edbc7f227b5fe';parent='8cdeaf7167a9dd1a1d6745c0765ab5fd0aa4af88';frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
def at(r,p):return subprocess.check_output(['git','-C',str(repo),'show',r+':'+p])
def cut(raw,anchor):
 start=raw.index(anchor);brace=raw.index(b'{',start);end=brace+1;depth=1
 while depth:depth+=(raw[end]==123)-(raw[end]==125);end+=1
 return raw[start:end]
p='crates/aspis-r1-cost-probe/src/verifier.rs';raw=at(frozen,p);body=cut(raw,b'fn query_with_geometry<H:Digest32>');candidate_body=cut(at(candidate,p),b'fn query_with_geometry<H:Digest32>');assert candidate_body==cut(at(parent,p),b'fn query_with_geometry<H:Digest32>')
query=b'let q=v.query(i);';helper=b'crate::fast_dots::four_dots(q,g)';assert body.count(query)==body.count(helper)==1
assert candidate_body.count(query)==candidate_body.count(helper)==1
candidate_context=candidate_body.replace(query,b'let q=SOURCE_QUERY(v,i);').replace(helper,b'SOURCE_DOTS(q,g)');assert candidate_context.replace(b'let q=SOURCE_QUERY(v,i);',query).replace(b'SOURCE_DOTS(q,g)',helper)==candidate_body
context=body.replace(query,b'let q=SOURCE_QUERY(v,i);').replace(helper,b'SOURCE_DOTS(q,g)');assert context.replace(b'let q=SOURCE_QUERY(v,i);',query).replace(b'SOURCE_DOTS(q,g)',helper)==body
# q is an immutable source binding. All code between/beyond calls remains in ctx.
assert not re.search(rb'let\s+mut\s+q\b',body)
all_sources=subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','--name-only',frozen,'crates/aspis-r1-cost-probe/src'],text=True).splitlines();callers=[]
for path in all_sources:
 if path.endswith('.rs'):
  source=at(frozen,path)
  for m in re.finditer(rb'crate::fast_dots::four_dots\s*\(',source):callers.append(dict(path=path,offset=m.start(),file_sha256=sha(source)))
assert len(callers)==1,callers
shared={}
for path in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs']:
 x=at(frozen,path);assert x==at(candidate,path)==at(parent,path);shared[path]=sha(x)
report=dict(candidate=candidate,parent=parent,frozen=frozen,features=['pool-adapter','private-leaf-salts'],caller=dict(path=p,file_sha256=sha(raw),body_sha256=sha(body),factored_sha256=sha(context),inverse_checked=True,parent_candidate_body_identical=True,frozen_context_independently_inverse_checked=True,candidate_body_sha256=sha(candidate_body),candidate_context_sha256=sha(candidate_context),query_source='AspisR1CuQuery.verifier.View.query',query_bound='CuSavingsQueryAccess.query_prefix_bound',consuming_theorem='AspisR1.CuSavingsPrefixCandidate10.caller_context'),sole_helper_calls=callers,shared_source_sha256=shared,shared_interpretation='Same exact source definitions and carriers for all nine Arithmetic fields on both sides; arbitrary result/failure/divergence computations, no algebraic/success/equivalence law. Universal theorem can instantiate original common callees directly. Concrete source array.from_fn admission proved separately by source_eq_build and consumed by sourceOld/sourceNew.')
outputs={'candidate-caller.source.rs':candidate_body,'candidate-caller.factored.rs':candidate_context,'caller.source.rs':body,'caller.factored.rs':context,'source-pins.json':(json.dumps(report,indent=2)+'\n').encode()}
for n,b in outputs.items():
 dest=tool/'prefix-candidate10-context'/n
 if a.check:assert dest.read_bytes()==b,n
 else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
print(json.dumps(dict(check=a.check,sole_caller=True,inverse_checked=True,unchanged_shared_helpers=True)))
