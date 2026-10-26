#!/usr/bin/env python3
"""Read-only source/receipt audit; never launches a proof or build."""
from pathlib import Path
import hashlib,json,re,subprocess,time
start=time.monotonic();root=Path(__file__).resolve().parents[2];b=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];rows=[]
for p in sorted(b.glob('PoolL_*/receipt.json')):
 x=json.loads(p.read_text());rows.append(x)
 for f,h in x['source_hashes'].items():
  if sha(p.parent/'sources'/f)!=h:errors.append('snapshot hash '+x['attempt']+' '+f)
 if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('caps '+x['attempt'])
 if x['swaps']!='0':errors.append('swaps '+x['attempt'])
lean=[x for x in rows if x['kind']=='lean'];kani=[x for x in rows if x['kind']=='kani']
if len(lean)!=100 or len(kani)!=15:errors.append('budget receipt mismatch')
source_receipts={}
for p in sorted((root/'lean').glob('PoolL_*.lean')):
 matching=[x for x in lean if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 if not matching:errors.append('no exact green '+p.name)
 else:source_receipts[p.name]=matching[-1]['attempt']
 if re.search(r'^\s*(axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+max(RecDepth|Heartbeats)',p.read_text(),re.M):errors.append('proof discipline '+p.name)
 for x in matching:
  if any('sorryAx' in line for line in x['print_axioms']):errors.append('unaccepted axioms '+p.name)
audit=json.loads((b/'PoolL_LEAN100/receipt.json').read_text())
if audit['exit_status'] or len(audit['print_axioms'])!=81:errors.append('final audit count/exit')
allowed={'propext','Classical.choice','Quot.sound'}
for line in audit['print_axioms']:
 names=re.search(r'\[([^]]*)\]',line)
 if names and not set(names.group(1).split(', '))<=allowed:errors.append('axioms '+line)
freeze=json.loads((b/'PoolL_FREEZE.json').read_text())
for f,pin in freeze['pins'].items():
 if sha(root/f)!=pin['sha256'] or (root/f).stat().st_size!=pin['bytes']:errors.append('frozen source '+f)
manifest=json.loads((root/'evidence/lowering2-20261026/Low2_build_manifest.json').read_text());counts=[]
for build in manifest['builds']:
 counts.append(len(build['repository_compiler_inputs']))
 for pin in build['repository_compiler_inputs']:
  if sha(root/pin['path'])!=pin['sha256']:errors.append('inherited compiler input '+pin['path'])
diff=subprocess.check_output(['git','diff','--name-only',freeze['revision']],cwd=root,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
for p in set(diff+untracked):
 if not (p.startswith('lean/PoolL_') or p.startswith('evidence/pool-nonint3-20261026/')):errors.append('scope '+p)
for p in b.rglob('*'):
 if p.is_file() and p.suffix in {'.olean','.ir','.elf','.so','.a','.tar','.gz','.llbc'}:errors.append('binary artifact '+str(p))
(b/'PoolL_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
summary={}
for kind,rs in [('lean',lean),('kani',kani)]:
 summary[kind]={'used':len(rs),'passed':sum(x['exit_status']==0 for x in rs),'failed':[x['attempt'] for x in rs if x['exit_status']!=0], 'wall_seconds':sum(x['wall_seconds'] for x in rs),'peak_rss_kib':max(int(x['peak_rss_kib']) for x in rs),'swaps':sum(int(x['swaps']) for x in rs)}
summary.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_tree_dirty=True,source_receipts=source_receipts,inherited_input_counts=counts,audited_top_theorems=len(audit['print_axioms']),validation_wall_seconds=time.monotonic()-start,errors=errors,exit=int(bool(errors)),claim='Source/receipt integrity and standard axioms only. Full handler/dispatcher/runtime/source-to-ELF closure remains open.')
(b/'PoolL_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='source_receipts'},indent=2));raise SystemExit(bool(errors))
