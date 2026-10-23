#!/usr/bin/env python3
"""Focused integrity/cut audit; completeness deliberately remains exit 2."""
import argparse,ast,collections,copy,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-repin2-20261023'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();checks=[]
a=argparse.ArgumentParser();a.add_argument('--gates',action='store_true');args=a.parse_args()
source=load(E/'source-inputs.json')
for r in source['files']+source['additional_workspace_inputs']:assert sha(R/r['path'])==r['sha256'],r['path']
assert len(source['files'])==7978 and sum(r['changed'] for r in source['files'])==5
checks.append('all 7978 current snapshot inputs rehashed; five changed/added source files')
for p in T.rglob('*.py'):ast.parse(p.read_text(),filename=str(p))
for r in load(E/'preflight.json')['generic_lean_sources']:assert sha(R/r['path'])==r['sha256']
checks.append('all Python scripts parse; retained generic Lean sources unchanged; no new Lean theorem')
expected=dict(default='d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0',devnet='2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922',pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
builds=load(E/'build-manifest.json');assert builds['source_revision']==source['source_revision'] and len(builds['builds'])==5
provenance=load(E/'comparison-provenance.json')
for b in builds['builds']:
 d=E/b['name'];r=load(d/'receipt.json');assert r['limits']==limits and r['swaps']==0
 reservation=load(d/'reservation.json');assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
 launcher=provenance['build_launchers'][b['name']];assert sha(R/launcher['path'])==launcher['sha256']
 if 'comparison' in b:
  c=b['comparison'];assert r['exit_status']==0 and c['byte_identical'] and c['sha256']==c['expected_sha256']==expected[c['mode']]
 else:assert b['name'] in ('build-default-v2','build-devnet-v1') and r['exit_status']==1
 for output in b['outputs']:
  local=d/Path(output['path']).name
  if local.exists():assert sha(local)==output['sha256'] and local.stat().st_size==output['bytes']
checks.append('three adopted hashes; all five raw build attempts, launcher pins, resource caps, reservations and revision correction retained')
for name in ['analysis-manifest.json','diff-manifest.json']:
 x=load(E/name);assert x['actual_source_revision']==source['source_revision']
 for r in x['artifacts']:
  p=E/Path(r['path']).name
  if p.exists():assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],p
  else:assert r in x['host_only']
for r in load(E/'generator-adapters.json'):
 assert sha(R/r['original'])==r['original_sha256'] and sha(R/r['adapted'])==r['adapted_sha256']
checks.append('all final compiler/ELF/comparison output pins and original/adapted generator hashes checked; large maps explicitly host-only')
for p in sorted(E.glob('*-invocation.json')):
 x=load(p);stem=p.name.removesuffix('-invocation.json');script=T/Path(x['target']).name
 if stem in ('collect-host-v1','prepare-host-v1','alias-mir-host-v1'):script=T/'historical'/(stem+'.py')
 assert sha(script)==x['script_sha256'],p
 expected_exit=1 if stem in ('collect-host-v1','prepare-host-v1') else 0
 receipt=load(E/(stem+'-receipt.json'));assert x['exit_status']==receipt['exit_status']==expected_exit,p
 assert receipt['limits']==limits and receipt['swaps']==0,p
 reservation=load(E/(stem+'-reservation.json'));assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
for rows in provenance['analysis_imports'].values():
 for r in rows:assert sha(R/r['path'])==r['sha256']
checks.append('every scoped analysis attempt/script/dependency/cap/reservation checked, including retained path/setup failures')
cfg=load(E/'cfg.json');oldcfg=load(B/'evidence/s10-repin-20261022/cfg.json')
assert sum(len(g['cuts']) for g in cfg['functions'])==140
for g in cfg['functions']:
 old=next(o for o in oldcfg['functions'] if o['mode']==g['mode'] and o['header'].split('(',1)[0]==g['header'].split('(',1)[0])
 assert old['edges']==g['edges']
 def valid(c,edges):
  reach=set(c['reachable_without_cut']);cut=c['cut'];target=c['target']
  return 0<=cut<g['blocks'] and 0<=target<g['blocks'] and cut!=target and cut not in reach and target not in reach and (0 in reach)==(cut!=0) and all(v==cut or u not in reach or v in reach for u,v in edges)
 for c in g['cuts']:
  assert valid(c,g['edges'])
  if c['cut']!=0:assert not valid(c,g['edges']+[[0,c['target']]])
order=load(E/'ordering-repin-map.json');assert order['all_140_preserved'] and not order['reselected_facts'] and order['coordinate_changes']==0 and order['changed_bodies']==2
checks.append('all 140 current CFG cuts plus bypass mutations; twelve edge lists unchanged, no reselected calls/block coordinates')
graphs=load(E/'elf-graphs.json')['artifacts'];cross=load(E/'elf-crosscheck.json')['artifacts']
for mode,g in graphs.items():
 unique={c['address']:c for c in g['calls']}
 assert len(unique)==(2202 if mode=='pool' else 1633)
 assert sum(c['kind']=='indirect' for c in unique.values())==(80 if mode=='pool' else 36)
 assert set(unique)=={c['address'] for c in cross[mode]['calls']}
 assert all(c==unique[c['address']] for c in g['calls'])
 assert cross[mode]['deployed']['sha256']==expected[mode] and not cross[mode]['debug_info_present']
checks.append('all unique LLVM-disassembled calls agree; duplicate symbol-alias records explicit; all adopted hashes and absent final DWARF confirmed')
commands=[]
for name,argv,expect in [('ordering-map.py',['--check'],0),('inventory.py',['--check','--require-complete'],2),('reconcile.py',['--check','--require-complete'],2),('check-callbacks.py',['--check'],0)]:
 cmd=[sys.executable,'-B',str(T/name),*argv];p=subprocess.run(cmd,cwd=R,text=True,capture_output=True);assert p.returncode==expect,(name,p.stdout,p.stderr)
 commands.append(dict(command=cmd,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
checks.append('deterministic ordering/ownership/change reconciliation; both completeness gates exit 2; callback replay and 189 negative controls')
assessment=load(E/'change-assessment.json');owners=load(E/'declaration-ownership.json');inv=load(E/'inventory.json')
assert assessment['child_generic_mir_unchanged'] and assessment['substantive_source_and_project_mir_delta_confined_to_adapter_caller_glue'] and not assessment['whole_source_delta_confined_to_adapter_files']
assert [len(r['declarations']) for r in assessment['modes']]==[193,193,0]
assert [r['remaining_alias_normalized_groups'] for r in assessment['modes']]==[40,40,0]
assert [r['mono_exact_deltas'] for r in assessment['modes']]==[32,32,0]
assert [r['llvm_emitted_text_deltas'] for r in assessment['modes']]==[94,94,0]
assert [r['elf_edge_multiset_deltas'] for r in assessment['modes']]==[97,97,0]
assert owners['records']==14249 and not owners['unassigned'] and not owners['complete']
assert len(inv['declarations'])==1046 and not inv['unassigned'] and not inv['assigned_twice'] and not inv['complete']
assert owners['overlay_sha256']==sha(B/'evidence/lead-repin-20261022/ownership.json') and owners['policy_sha256']==sha(T/'historical/ownership-policy.py')
children=load(E/'child-pins.json');assert len(children['helpers'])==27
checks.append('all exact MIR/mono/LLVM/ELF deltas classified; unchanged children; out-of-line library clone exception explicit; 1046 ELF and 14249 generic ownership proposals remain incomplete')
# A task changes only its evidence/tools and the requested inventory addendum.
changed=subprocess.check_output(['git','diff','--name-only',source['source_revision']],cwd=R,text=True).splitlines()
allowed=['tools/s10-repin2-20261023/','docs/research/100bit-spend-path-20261013/evidence/s10-repin2-20261023/']
assert all(any(p.startswith(a) for a in allowed) or p=='docs/research/100bit-spend-path-20261013/design/S10-INVENTORY-20261021.md' for p in changed),changed
checks.append('no shipped file, old certificate, Lean source or session-A candidate changed')
u=resource.getrusage(resource.RUSAGE_SELF);revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
result=dict(schema='s10-owned-adapter-focused-audit-v1',target=str(Path(__file__).relative_to(R)),source_revision=revision,actual_compiler_source_revision=source['source_revision'],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,print_axioms='N/A: no new Lean statement or compilation; retained generic graph mathematics only',checks=checks,commands=commands,release_claim=False,completeness_gate_exit_status=2)
pins=dict(source_revision=revision,toolpins={str(p.relative_to(R)):sha(p) for p in sorted(T.rglob('*.py'))},inputpins={str(p.relative_to(R)):sha(p) for p in sorted(E.rglob('*')) if p.is_file() and p.name not in ('validation.json','final-pins.json')})
pins['inputpins'][str((B/'design/S10-INVENTORY-20261021.md').relative_to(R))]=sha(B/'design/S10-INVENTORY-20261021.md')
(E/'final-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n');(E/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(exit_status=2 if args.gates else 0,checks=len(checks),wall_seconds=result['wall_seconds'],completeness='INCOMPLETE')))
if args.gates:raise SystemExit(2)
