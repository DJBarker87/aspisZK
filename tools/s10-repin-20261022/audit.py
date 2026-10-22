#!/usr/bin/env python3
"""Focused integrity audit and independent graph mutations; no release replay."""
import argparse,collections,copy,hashlib,importlib.util,json,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-repin-20261022'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
a=argparse.ArgumentParser();a.add_argument('--gates',action='store_true');args=a.parse_args();checks=[]
sources=load(E/'source-inputs.json')
assert sources['source_revision']=='7acf5cfb5fa49f4cf5d8e69566ba8221189c31ac'
for r in sources['files']+sources['additional_workspace_inputs']:assert sha(R/r['path'])==r['sha256'],r['path']
assert len(sources['files'])==488 and sum(r['changed'] for r in sources['files'])==16
checks.append('every current source input rehashed; sixteen historical census differences retained')
expected=dict(default='40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0',devnet='12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f',pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
builds=load(E/'build-manifest.json')
assert builds['source_revision']==sources['source_revision'] and builds['receipt_revision_correction']
assert len(builds['builds'])==4
for b in builds['builds']:
 d=E/b['name'];r=load(d/'receipt.json');assert r['limits']==limits and r['swaps']==0
 assert b['actual_source_revision']==sources['source_revision']
 if 'comparison' in b:
  c=b['comparison'];assert r['exit_status']==0 and c['byte_identical'] and c['sha256']==c['expected_sha256']==expected[c['mode']]
 else:assert b['name']=='build-default-v1' and r['exit_status']==1
 for p in b['outputs']:
  local=d/Path(p['path']).name
  if local.exists():assert sha(local)==p['sha256'] and local.stat().st_size==p['bytes']
checks.append('three adopted artifact hashes and all raw build receipts/caps checked; failed preflight and revision correction retained')
for m in ['analysis-manifest.json','diff-manifest.json']:
 x=load(E/m);assert x['actual_source_revision']==sources['source_revision']
 for r in x['artifacts']:
  local=E/Path(r['path']).name
  if local.exists():assert sha(local)==r['sha256'] and local.stat().st_size==r['bytes'],local
  else:assert r in x['host_only']
for r in load(E/'generator-adapters.json'):
 assert sha(R/r['original'])==r['original_sha256'] and sha(R/r['adapted'])==r['adapted_sha256']
checks.append('all collected artifact and retained generator/adaptor pins checked; large compiler maps explicitly host-only')
for p in sorted(E.glob('*-invocation.json')):
 x=load(p);assert x['exit_status']==0,p
 name=Path(x['target']).name;script=T/name
 if p.name=='diff-host-invocation.json':script=T/'historical/diff-host-v1.py'
 if p.name=='diff-host-v2-invocation.json':script=T/'historical/diff-host-v2.py'
 assert sha(script)==x['script_sha256'],p
 receipt=load(E/(p.name.replace('-invocation.json','-receipt.json')))
 assert receipt['exit_status']==0 and receipt['limits']==limits and receipt['swaps']==0,p
 reservation=load(E/(p.name.replace('-invocation.json','-reservation.json')))
 assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
checks.append('every final and historical scoped analysis script/exit/resource/reservation receipt checked')
cfg=load(E/'cfg.json')
def valid(g,c):
 reach=set(c['reachable_without_cut']);cut=c['cut'];target=c['target']
 return 0<=cut<g['blocks'] and 0<=target<g['blocks'] and cut!=target and (0 in reach)==(cut!=0) and cut not in reach and target not in reach and all(v==cut or u not in reach or v in reach for u,v in g['edges'])
assert sum(len(g['cuts']) for g in cfg['functions'])==140
for g in cfg['functions']:
 assert all(0<=u<g['blocks'] and 0<=v<g['blocks'] for u,v in g['edges'])
 for c in g['cuts']:assert valid(g,c)
 # A direct entry-to-target bypass must be rejected for every non-root cut.
 for c in g['cuts']:
  if c['cut']==0:continue
  bad=copy.deepcopy(g);bad['edges'].append([0,c['target']]);assert not valid(bad,c)
checks.append('all 140 new cut witnesses checked independently; every applicable entry-to-target bypass rejected')
commands=[]
for name,argv,expect in [('ordering-map.py',['--check'],0),('inventory.py',['--check','--require-complete'],2),('reconcile.py',['--check','--require-complete'],2),('check-callbacks.py',['--check'],0)]:
 cmd=[sys.executable,'-B',str(T/name),*argv];p=subprocess.run(cmd,cwd=R,text=True,capture_output=True)
 assert p.returncode==expect,(name,p.stdout,p.stderr)
 commands.append(dict(command=cmd,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
checks.append('ordering/ownership/change outputs regenerate; both completeness gates exit 2; callback replay retains 189 negative controls')
elf=load(E/'elf-crosscheck.json')['artifacts'];graphs=load(E/'elf-graphs.json')['artifacts']
assert {m:len(g['calls']) for m,g in elf.items()}==dict(default=1603,devnet=1603,pool=2202)
for m,g in elf.items():
 assert g['deployed']['sha256']==expected[m] and not g['debug_info_present']
 assert {c['address'] for c in g['calls']}=={c['address'] for c in graphs[m]['calls']}
 assert all(c['kind'] in ('direct','indirect','syscall') for c in g['calls'])
checks.append('new instruction call counts, all adopted hashes and absent DWARF corroborated')
assessment=load(E/'change-assessment.json')
assert assessment['observed_frozen_mir_substantive_delta_confined_to_adopted_files_and_inline_callers']
assert not assessment['whole_source_delta_confined_to_three_files'] and len(assessment['other_source_differences'])==13
assert [len(r['declarations']) for r in assessment['modes']]==[17,17,0]
assert [r['mono_exact_deltas'] for r in assessment['modes']]==[91,91,0]
assert [r['elf_edge_multiset_deltas'] for r in assessment['modes']]==[31,31,0]
owners=load(E/'declaration-ownership.json');assert owners['records']==14189 and not owners['unassigned'] and not owners['complete']
assert owners['overlay_sha256']==sha(B/'evidence/lead-repin-20261022/ownership.json')
assert owners['policy_sha256']==sha(T/'historical/ownership-policy.py')
checks.append('every changed body explained; exact mono/edge deltas retained; host generic census and lead overlay bound without completeness claim')
u=resource.getrusage(resource.RUSAGE_SELF)
toolpins={str(p.relative_to(R)):sha(p) for p in sorted(T.rglob('*.py'))}
inputpins={str(p.relative_to(R)):sha(p) for p in sorted(E.rglob('*')) if p.is_file() and p.name not in ('validation.json','final-pins.json')}
report=B/'design/S10-INVENTORY-20261021.md';inputpins[str(report.relative_to(R))]=sha(report)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
result=dict(schema='s10-adopted-focused-audit-v1',target=str(Path(__file__).relative_to(R)),source_revision=revision,
 actual_compiler_source_revision=sources['source_revision'],exit_status=0,wall_seconds=time.monotonic()-start,
 peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,
 print_axioms='N/A: no new Lean statement or compilation; historical generic graph mathematics only',checks=checks,commands=commands,
 release_claim=False,completeness_gate_exit_status=2)
(E/'final-pins.json').write_text(json.dumps(dict(toolpins=toolpins,inputpins=inputpins,source_revision=revision),indent=2,sort_keys=True)+'\n')
(E/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(exit_status=2 if args.gates else 0,checks=len(checks),wall_seconds=result['wall_seconds'],completeness='INCOMPLETE')))
if args.gates:raise SystemExit(2)
