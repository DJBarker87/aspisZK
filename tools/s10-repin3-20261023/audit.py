#!/usr/bin/env python3
"""Focused H5 receipt audit; no release/completeness claim."""
import ast,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-repin3-20261023'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();checks=[]
source=load(E/'source-inputs.json')
for r in source['files']+source['additional_workspace_inputs']:assert sha(R/r['path'])==r['sha256'],r['path']
assert len(source['files'])==7978 and sum(r['changed'] for r in source['files'])==5
for r in load(E/'snapshot-exclusions.json')['excluded']:assert sha(R/r['path'])==r['sha256']
for p in T.rglob('*.py'):ast.parse(p.read_text(),filename=str(p))
for r in load(E/'preflight.json')['generic_lean_sources']:assert sha(R/r['path'])==r['sha256']
checks.append('selected snapshot, explicit exclusions and retained generic Lean source pins; all Python parses')
expected=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def resources(receipt,reservation):
 assert receipt['limits']==limits and receipt['swaps']==0
 assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
builds=load(E/'build-manifest.json');assert builds['source_revision']==source['source_revision'] and len(builds['builds'])==3
for b in builds['builds']:
 d=E/b['name'];r=load(d/'receipt.json');resources(r,load(d/'reservation.json'));assert r['exit_status']==0
 c=b['comparison'];assert c['sha256']==expected[c['mode']]
 assert load(d/'command.json')['wrapper_sha256']==sha(T/'rustc-diagnostics.py')
 if c['mode']=='devnet':assert c['expected_sha256'] is None and not c['byte_identical']
 else:assert c['expected_sha256']==expected[c['mode']] and c['byte_identical']
 for o in b['outputs']:
  p=d/Path(o['path']).name
  if p.exists():assert sha(p)==o['sha256'] and p.stat().st_size==o['bytes']
checks.append('three successful optimized capped builds, zero swap, reservations, exact expected/discovered pins and raw revision correction')
for name in ['analysis-manifest.json','diff-manifest.json']:
 x=load(E/name);assert x['actual_source_revision']==source['source_revision']
 for r in x['artifacts']:
  p=E/Path(r['path']).name
  if p.exists():assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],p
  else:assert r in x['host_only']
for r in load(E/'generator-adapters.json'):
 assert sha(R/r['original'])==r['original_sha256'] and sha(R/r['adapted'])==r['adapted_sha256']
for r in load(E/'comparison-provenance.json')['comparison_inputs']:
 assert sha(R/r['path'])==r['sha256']
for p in E.glob('*-invocation.json'):
 x=load(p);stem=p.name.removesuffix('-invocation.json');script=T/Path(x['target']).name
 if stem=='elf-symbol-kinds-host':script=T/'historical/elf-symbol-kinds-host-v1.py'
 assert sha(script)==x['script_sha256'],p
 receipt=load(E/(stem+'-receipt.json'));assert receipt['exit_status']==x['exit_status']==(1 if stem in ('collect-host-v2','elf-symbol-kinds-host') else 0),p
 resources(receipt,load(E/(stem+'-reservation.json')))
checks.append('all analysis outputs, adapted/original algorithms, scoped invocations and retained setup failures pinned')
cfg=load(E/'cfg.json');assert sum(len(g['cuts']) for g in cfg['functions'])==140
oldcfg=load(B/'evidence/s10-repin2-20261023/cfg.json')
for g in cfg['functions']:
 old=next(o for o in oldcfg['functions'] if o['mode']==g['mode'] and o['header']==g['header'])
 assert old['edges']==g['edges']
 def valid(c,edges):
  reach=set(c['reachable_without_cut']);cut=c['cut'];target=c['target']
  return 0<=cut<g['blocks'] and 0<=target<g['blocks'] and cut!=target and cut not in reach and target not in reach and (0 in reach)==(cut!=0) and all(v==cut or u not in reach or v in reach for u,v in edges)
 for c in g['cuts']:
  assert valid(c,g['edges'])
  if c['cut']!=0:assert not valid(c,g['edges']+[[0,c['target']]])
order=load(E/'ordering-repin-map.json');assert order['all_140_preserved'] and not order['reselected_facts']
assert order['coordinate_changes']==order['changed_bodies']==0
checks.append('all 140 current graph cuts, independent bypass mutations and explicit old/new call selection map')
graphs=load(E/'elf-graphs.json')['artifacts'];cross=load(E/'elf-crosscheck.json')['artifacts']
for mode,g in graphs.items():
 unique={c['address']:c for c in g['calls']}
 assert set(unique)=={c['address'] for c in cross[mode]['calls']}
 assert all(c==unique[c['address']] for c in g['calls'])
 assert cross[mode]['deployed']['sha256']==expected[mode] and not cross[mode]['debug_info_present']
checks.append('all physical call instructions independently decoded by LLVM, aliases agree, final DWARF absence explicit')
commands=[]
for name,args,expected_exit in [('ordering-map.py',['--check'],0),('inventory.py',['--check','--require-complete'],2),('reconcile.py',['--check','--require-complete'],2),('check-callbacks.py',['--check'],0)]:
 cmd=[sys.executable,'-B',str(T/name),*args];p=subprocess.run(cmd,cwd=R,text=True,capture_output=True);assert p.returncode==expected_exit,(name,p.stdout,p.stderr)
 commands.append(dict(command=cmd,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
checks.append('deterministic maps and callback negative controls; both completeness gates exit 2')
a=load(E/'change-assessment.json');inv=load(E/'inventory.json');owners=load(E/'declaration-ownership.json')
assert not a['child_generic_mir_unchanged'] and not a['substantive_source_and_project_mir_delta_confined_to_adapter_caller_glue']
assert not inv['unassigned'] and not inv['assigned_twice'] and not inv['complete'] and not owners['unassigned'] and not owners['complete']
assert owners['overlay_sha256']==sha(B/'evidence/lead-repin-20261022/ownership.json')
assert owners['policy_sha256']==sha(R/'tools/s10-repin2-20261023/historical/ownership-policy.py')
assert len(load(E/'child-pins.json')['helpers'])==27
assert [len(m['declarations']) for m in a['modes']]==[57,57,1]
assert [m['mono_exact_deltas'] for m in a['modes']]==[170,170,0]
assert [m['llvm_emitted_text_deltas'] for m in a['modes']]==[167,167,4]
assert [m['elf_edge_multiset_deltas'] for m in a['modes']]==[44,44,0]
assert owners['records']==14227 and len(inv['declarations'])==1040
checks.append('exact deltas and H5 child changes explicit, overlay/policy pinned, ownership and reachability remain proposals/lower bounds')
changed=subprocess.check_output(['git','diff','--name-only',source['source_revision']],cwd=R,text=True).splitlines()
assert all(p.startswith(('tools/s10-repin3-20261023/','docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/')) or p=='docs/research/100bit-spend-path-20261013/design/S10-INVENTORY-20261021.md' for p in changed),changed
checks.append('no shipped file, old certificate, Lean module or session-A candidate changed')
u=resource.getrusage(resource.RUSAGE_SELF);revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
result=dict(target=str(Path(__file__).relative_to(R)),source_revision=revision,actual_compiler_source_revision=source['source_revision'],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,print_axioms='N/A: no new Lean theorem or compilation; retained generic graph mathematics only',checks=checks,commands=commands,release_claim=False,completeness_gate_exit_status=2)
pins=dict(source_revision=revision,toolpins={str(p.relative_to(R)):sha(p) for p in sorted(T.rglob('*.py'))},inputpins={str(p.relative_to(R)):sha(p) for p in sorted(E.rglob('*')) if p.is_file() and p.name not in ('validation.json','final-pins.json')})
pins['inputpins'][str((B/'design/S10-INVENTORY-20261021.md').relative_to(R))]=sha(B/'design/S10-INVENTORY-20261021.md')
(E/'final-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n');(E/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(exit_status=0,checks=len(checks),wall_seconds=result['wall_seconds'],completeness='INCOMPLETE')))
