"""Additive two-row admission: no inherited validator or ledger is modified."""
from pathlib import Path
import argparse,json,hashlib,lzma,re,subprocess,copy
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads((E/p).read_text())
def validate():
 audit=read('NGT_AUDIT.json');assert audit['status']=='PASS'
 raw=read('NGT_audit/batch0/proof0.json');assert raw['exit_status']==0
 assert {r['root'] for r in raw['results']}==set(read('NGT_AUDIT_ROOTS.json')['groups'][0])
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw['results'])
 fixture=read('NGT_audit/fixtures/fixtures.json');assert len(fixture['results'])==8 and fixture['exit_status']==0
 assert all(r['equal'] and (bool(r['walked_axioms']) if i<4 else not r['walked_axioms']) for i,r in enumerate(fixture['results']))
 scan=[json.loads(l) for l in (E/'NGT_LOADED_scan.jsonl').read_text().splitlines()]
 assert len(scan)==13492 and all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
 assert read('NGT_L048/receipt.json')['exit_status']==0
 source=read('NGT_SOURCE_FIDELITY.json');assert not source['source_errors'] and len(source['unchanged_method_continuity'])==4
 assert all(v['byte_identical'] for v in source['unchanged_method_continuity'].values())
 for n,h in read('NGT_FROZEN_FILE_PINS.json').items():assert sha((R/n).read_bytes())==h,n
 meta=read('NGT_METADATA_MANIFEST.json');native=[]
 for n in range(1,43):
  a=f'NGT_K{n:03d}';x=read(a+'/receipt.json');g=read(a+'-graph-check.json');l=read(a+'-lock-check.json')
  assert g['graph_matches_frozen'] and l['unchanged']
  pinned=meta[a+'-graph.json'];b=lzma.decompress((E/pinned['artifact']).read_bytes());assert sha(b)==g['graph_sha256']==pinned['sha256']
  # Complete per-crate features are in the hash-addressed metadata input.
  full=json.loads(b);assert len(full['packages'])==g['resolved_packages']
  features=next(r['features'] for r in g['selected_closure'] if r['name']=='aspis-r1-cost-probe')
  assert set(features)=={'default','private-leaf-salts','optimized-terminal','program-build'}
  assert x['env']['CARGO_NET_OFFLINE']=='true' and x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  admission=read(a+'-admission.json');assert admission['exit']==0 and admission['reservation']['allowed'] is True
  assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  for path,h in x['source_hashes'].items():assert sha((E/a/'sources'/path).read_bytes())==h,path
  if n>=3:
   negative=n%2==0;assert x['exit_status']==int(negative)
   log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in log
   assert 'timed out' not in log.lower()
   native.append(dict(attempt=a,harness=x['module'],exit=x['exit_status'],negative=negative,receipt=a+'/receipt.json'))
 # Every final top root is from an exact successful source snapshot. Failed
 # elaborations (including diagnostic sorryAx output) are never admitted.
 required={'NGT_L004':'NGT_Emitted','NGT_L005':'NGT_EmittedEq','NGT_L025':'NGT_Reduction','NGT_L027':'NGT_SamplerLaw','NGT_L029':'NGT_RuntimeDomain','NGT_L036':'NGT_FrameChain','NGT_L038':'NGT_BlockAssociation','NGT_L039':'NGT_CallerInterface','NGT_L040':'NGT_COMBINED_IMPORT'}
 for a,n in required.items():
  x=read(a+'/receipt.json');assert x['exit_status']==0
  assert sha((E/(n+'.lean')).read_bytes())==x['source_hashes']['NGT_generated/'+n+'.lean']
  assert all('sorryAx' not in line for line in x['print_axioms'])
 renames=read('NGT_RETARGET_REUSE.json')['renames']
 attempts_now=[json.loads(l) for l in (E/'NGT_ATTEMPTS.jsonl').read_text().splitlines()]
 for n in renames.values():
  successful=[r for r in attempts_now if r['kind']=='lean' and r['module']==n and r['exit_status']==0];assert successful,n
  x=read(successful[-1]['attempt']+'/receipt.json');assert sha((E/(n+'.lean')).read_bytes())==x['source_hashes']['NGT_generated/'+n+'.lean']
 for p in E.glob('NGT_NEP_proof0_*REACHABLE.txt.xz'):assert b'XRn_Join' not in lzma.decompress(p.read_bytes())
 closed=read('NGT_CLOSED.json');assert closed['status']=='CLOSED' and {r['row'] for r in closed['functions']}=={'TX1:169','TX1:170'}
 assert all(r['status']=='CLOSED' and not r['inner_hypotheses_remaining'] for r in closed['functions'])
 ledger_path=R/'evidence/ledger8-20261105/NGJ_LEDGER.json.xz';baseline=json.loads(lzma.decompress(ledger_path.read_bytes()));new=copy.deepcopy(baseline)
 for r in new['rows']:
  if r['row'] in {'TX1:169','TX1:170'}:
   assert r['composed_status']=='OPEN';packet=next(p for p in closed['functions'] if p['row']==r['row']);assert r['function']==packet['function']
   r['composed_status']='CLOSED';r['NGT_certificate']=packet;r['NGT_provider']='NGT_';r['NGT_route']='(y)/(ai) hybrid'
 for old,r in zip(baseline['rows'],new['rows']):
  if old['row'] not in {'TX1:169','TX1:170'}:assert old==r
 attempts=[json.loads(l) for l in (E/'NGT_ATTEMPTS.jsonl').read_text().splitlines()]
 counts=dict(kani=sum(x['kind']=='kani' for x in attempts),lean_support=sum(x['kind'] not in ['kani','extract'] for x in attempts),extraction=sum(x['kind']=='extract' for x in attempts));assert counts['kani']<=80 and counts['lean_support']<=60 and counts['extraction']<=1
 assert all(not (p.is_file() and p.stat().st_size>20_000_000) for p in E.rglob('*'))
 return dict(status='PASS',new_rows=['TX1:169','TX1:170'],inherited_rows_preserved=len(baseline['rows'])-2,baseline_sha256=sha(ledger_path.read_bytes()),positive_native=len([x for x in native if not x['negative']]),matched_failing_controls=len([x for x in native if x['negative']]),raw_roots=len(raw['results']),scan_modules=len(scan),budget_used=counts,frozen_files=source['frozen_files'],security_target_established=False)
if __name__=='__main__':
 x=validate();print(json.dumps(x,indent=1))
