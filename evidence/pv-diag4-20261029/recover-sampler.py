from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).parent;B='docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/'
git=lambda p:subprocess.check_output(['git','show','HEAD:'+p]);sha=lambda b:hashlib.sha256(b).hexdigest()
paths=[B+'continuation/translation-sampler-001-audit.json',B+'stage3/sampler-normalization.json']+[B+f'stage3/{i}-{s}.json' for i in [11200,11202,11205,11207,11209,11210] for s in ['input','receipt']]
records={p:dict(sha256=sha(git(p)),record=json.loads(git(p))) for p in paths}
a=json.loads(git(paths[0]));n=json.loads(git(paths[1]));sources={}
for kind in ['Funs','Types']:
 p=B+f'continuation/generated-sampler/ProverRwSampler/{kind}.lean';raw=git(p);assert sha(raw)==a['artifacts'][kind+'.lean']['sha256']
 tracked='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwSampler/'+kind+'.lean';tracked=tracked if kind=='Funs' else p;actual=git(tracked)
 if kind=='Funs':
  assert sha(raw)==n['input_sha256'];assert raw.count(n['replacement'][0].encode())==n['count'];assert raw.replace(*[x.encode() for x in n['replacement']])==actual;assert sha(actual)==n['output_sha256']
 else:assert actual==raw
 sources['ProverRwSampler.'+kind]=dict(path=tracked,sha256=sha(actual),blob=subprocess.check_output(['git','rev-parse','HEAD:'+tracked],text=True).strip(),generation_sha256=sha(raw),qualification='historical explicit backend shift-numeral compatibility adaptation' if kind=='Funs' else 'byte-identical generation')
 (D/'source-inputs'/('ProverRwSampler.'+kind+'.lean.txt')).write_bytes(actual)
# Objects link generation 11202 -> first successful unchanged arithmetic importer 11205.
r={i:json.loads(git(B+f'stage3/{i}-receipt.json')) for i in [11200,11202,11205,11207,11209,11210]}
print({i:list(v) for i,v in r.items()})
(D/'sampler-generation-chain.json').write_text(json.dumps(dict(rule='h7(1) graph has neither sampler entry; h7(2) generation recovered with explicit historical adaptation; STEP4 unnecessary if association checks hold',records=records,sources=sources),indent=2)+'\n')
graphpath='docs/research/100bit-spend-path-20261013/evidence/import-union-20261022/host-module-graph.json';graph=json.loads(git(graphpath));assert not any(m in graph for m in sources)
envpath=B+'stage3/environment-audit.json';env=json.loads(git(envpath));assert env['all_recorded_dependency_objects_still_match']
for i in [11202,11205]:assert r[i]['exit_status']==0
assert r[11202]['source_sha256']==sources['ProverRwSampler.Funs']['sha256']
# Input snapshots and corresponding accepted receipts tie the unchanged importer
# to the normalized generation, not just a same-name file.
for i in [11200,11202,11205]:
 snap=git(B+f'stage3/{i}.lean.txt');assert sha(snap)==r[i]['source_sha256']
arithmetic='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSamplerArithmetic.lean';assert sha(git(arithmetic))==r[11205]['source_sha256']
d=json.loads((D/'sampler-generation-chain.json').read_text());d.update(graph_sha256=sha(git(graphpath)),graph_entries={m:graph.get(m) for m in sources},historical_environment=dict(path=envpath,sha256=sha(git(envpath)),record=env),unchanged_importer=dict(path=arithmetic,sha256=sha(git(arithmetic)),generation_receipt=B+'stage3/11205-receipt.json'))
(D/'sampler-generation-chain.json').write_text(json.dumps(d,indent=2)+'\n')
