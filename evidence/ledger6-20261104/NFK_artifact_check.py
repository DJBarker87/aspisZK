#!/usr/bin/env python3
"""Focused final output/source-pin check, with no slice/prover replay."""
import ast,hashlib,json,lzma,resource,subprocess,sys,time
from pathlib import Path
import NFK_validate as v
E=Path(__file__).resolve().parent
start=time.monotonic()
raw=lzma.decompress((E/'NFK_LEDGER.json.xz').read_bytes())
v.require(v.sha(raw)==(E/'NFK_LEDGER.json.sha256').read_text().strip(),'ledger transport hash')
d=json.loads(raw)
v.require((E/'NFK_LEDGER.md').read_text()==v.markdown(d),'canonical markdown drift')
v.require(d['NFK_coverage']['all_rows']==dict(total=587,CLOSED=219,QUALIFIED=2,OPEN=366),'coverage')
v.require(set(d['NFK_qualified_rows'])==v.QUALIFIED,'qualification set')
v.require({r['row'] for r in d['NFK_rejected_slice_closures']}==v.QUALIFIED,'closure reconciliation')
v.require(d['NFK_slices']['S']['roots_CLOSED']==7 and d['NFK_slices']['Q']['roots_CLOSED']==0,'root counts')
v.require(d['NFK_trust_usage']['RuntimeReturnData']['closed_rows']==['TX2:219'],'return-data consumer')
v.require(d['NFK_trust_usage']['RuntimeMemcmp']['closed_rows']==['TX2:226'],'memcmp consumer')
for name in ['NFK_FINAL','NFK_TESTS']:
 receipt=json.loads((E/(name+'.json')).read_bytes())
 v.require(receipt['exit_status']==0,'failed final receipt: '+name)
 for path,digest in receipt['source_sha256'].items():
  current=(E/path).read_bytes()
  if v.sha(current)==digest:continue
  v.require(path=='NFK_validate.py','source drift: '+path)
  old=subprocess.check_output(['git','show','2267b6d8439:evidence/ledger6-20261104/NFK_validate.py'],cwd=v.R)
  v.require(v.sha(old)==digest,'historical status source pin')
  def semantics(raw):
   tree=ast.parse(raw);tree.body=[n for n in tree.body if not(isinstance(n,ast.FunctionDef) and n.name=='markdown')]
   return ast.dump(tree,include_attributes=False)
  v.require(semantics(old)==semantics(current),'non-reporting validator drift')
final=json.loads((E/'NFK_FINAL.stdout').read_bytes())
for short,key in [('coverage','NFK_coverage'),('unique_functions','NFK_unique_functions'),('slices','NFK_slices'),('trust','NFK_trust_usage'),('rejected','NFK_rejected_slice_closures')]:v.require(final[short]==d[key],'final stdout drift: '+short)
v.require(not any(p.stat().st_size>20_000_000 for p in E.iterdir() if p.is_file()),'oversize artifact')
outputs={p.name:dict(bytes=p.stat().st_size,sha256=v.sha(p.read_bytes())) for p in sorted(E.iterdir()) if p.is_file() and p.name not in {'NFK_OUTPUTS.json','NFK_ARTIFACTS.json','NFK_ATTEMPTS.jsonl'}}
(E/'NFK_OUTPUTS.json').write_text(v.encode(outputs))
r=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(attempt='NFK_ARTIFACTS',target='evidence/ledger6-20261104/NFK_artifact_check.py',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=r.ru_maxrss if sys.platform=='darwin' else r.ru_maxrss*1024,swap='unmeasured Python status check; no prover process',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=v.R,text=True).strip(),source_sha256=v.sha(Path(__file__).read_bytes()),print_axioms='N/A: Python artifact checks; no new proof audit',lean_runs=0,kani_runs=0,checks='compressed transport, canonical report, source receipt pins, totals, qualification, roots, trust consumers, stdout reconciliation, sizes')
(E/'NFK_ARTIFACTS.json').write_text(v.encode(receipt))
with (E/'NFK_ATTEMPTS.jsonl').open('a') as stream:stream.write(json.dumps(receipt,sort_keys=True)+'\n')
print(v.encode(receipt))
