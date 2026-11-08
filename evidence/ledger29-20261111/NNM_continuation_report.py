"""Metadata-only continuation coverage and resource record; no prover invocation."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())
plan=J(E/'NNM_CONTINUATION_PLAN.json')
expected={r['root']:r for w in plan['windows']for r in w['roots']}
assert len(expected)==63
attempts=[];done={}
for p in sorted(E.glob('NNM_L*/receipt.json')):
 r=J(p)
 if int(r['attempt'][-3:])<=60:continue
 assert r['kind']=='audit' and r['command']==['python3','NNM_batch.py',r['module']]
 assert r['timeout']==180 and r['env']['LEAN_PATH'].split(':')[0]==plan['retained_export']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 g=int(r['module'].removeprefix('batch'));p=E/'NNM_audit'/r['module']/f'proof{g}.json'
 result=J(p) if p.exists() else None
 if result:
  assert result['exit_status']==0
  for z in result['results']:
   assert z['root']in expected and z['root']not in done
   assert set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
   assert z['equal']
   done[z['root']]=dict(expected[z['root']],attempt=r['attempt'],raw_result=z)
 attempts.append(dict(attempt=r['attempt'],exact_target=r['module'],command=r['command'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],receipt=r['attempt']+'/receipt.json',print_axioms=result['print_axioms']if result else [],completed_roots=len(result['results'])if result else 0))
missing=sorted(set(expected)-set(done));assert not missing,missing
out=dict(status='PASS',input_revision='be71831b3a3',required_missing_roots=63,completed_roots=len(done),missing_roots=missing,attempts=attempts,completed=[done[n]for n in sorted(done)],scopes_used=len(attempts),authorized_scopes=40,unused_scopes=40-len(attempts),unused_reason='All63 assigned missing roots completed. No remaining raw-walk member; repeat audits, new Lean modules, extraction and Kani are excluded by this continuation.',same_optimized_binary_sha256=J(E/'NNM_RAW_BINARY.json')['sha256'],standard_axioms_only=True,retained_export=plan['retained_export'],combined_import='NNM_COMBINED_IMPORT',caps_raised=False,timeout_raised=False,lean_compiles=0,kani=0,extraction=0,repeated_completed_windows=0,repeated_statement_audits=0,repeated_whole_import_scans=0,metadata_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NNM_CONTINUATION_RESULTS.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({k:out[k]for k in ['status','completed_roots','scopes_used','unused_scopes']}))
