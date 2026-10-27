"""Check local receipts/source snapshots; no prover invocation."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;errors=[];rows=[];axioms=[]
allowed={'propext','Classical.choice','Quot.sound'}
for kind,limit in [('L',100),('K',10)]:
 paths=sorted(E.glob('XRk_'+kind+'*/receipt.json'))
 if len(paths)>limit:errors.append('budget exceeded '+kind)
 for p in paths:
  x=json.loads(p.read_text())
  for name,sha in x['source_hashes'].items():
   q=p.parent/'sources'/name
   if not q.exists() or hashlib.sha256(q.read_bytes()).hexdigest()!=sha:errors.append('snapshot '+str(q))
  if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('caps '+x['attempt'])
  if int(x['swaps']):errors.append('swap '+x['attempt'])
  if kind=='L' and x['exit_status']==0:
   for line in x['print_axioms']:
    m=re.search(r'\[([^]]*)\]',line,re.S)
    if m and not {n.strip() for n in m[1].split(',') if n.strip()}<=allowed:errors.append('axioms '+x['attempt']+' '+line)
    axioms.append({'attempt':x['attempt'],'line':line})
  rows.append({'attempt':x['attempt'],'kind':kind,'exit':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':int(x['peak_rss_kib']),'swaps':int(x['swaps'])})
for name in ['ARX_Root','Rc10_Top']:
 before=(E/f'XRk_{name}.BEFORE.lean.txt').read_bytes();after=(E/f'XRk_{name}.AFTER.lean.txt').read_bytes()
 if before!=after or before!=Path('lean/'+name+'.lean').read_bytes():errors.append('top changed '+name)
for pin in json.loads((E/'XRk_recount.json').read_text())['baseline']:
 if hashlib.sha256(Path(pin['path']).read_bytes()).hexdigest()!=pin['sha256']:errors.append('pin changed '+pin['path'])
ad=json.loads((E/'XRk_adapter_changes.json').read_text())
if hashlib.sha256(Path(ad['input']).read_bytes()).hexdigest()!=ad['input_sha256']:errors.append('adapter input drift')
if hashlib.sha256((E/'XRk_Funs.lean').read_bytes()).hexdigest()!=ad['output_sha256']:errors.append('adapter output drift')
for p in E.glob('XRk_*.lean'):
 if re.search(r'^\s*(axiom|sorry|admit)\b',p.read_text(),re.M):errors.append('proof hole '+p.name)
base=subprocess.check_output(['git','rev-parse','c755d3ed8c^'],text=True).strip()
paths=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
for p in paths:
 if not p.startswith('evidence/extraction-assoc3-20261027/'):errors.append('scope '+p)
 if Path(p).suffix in {'.olean','.ilean','.ir','.elf','.a','.so','.tar','.gz'}:errors.append('binary '+p)
allocations=sorted(E.glob('XRk_L[0-9][0-9][0-9].json'))
if len(allocations)>100:errors.append('allocation limit')
missing=[p.stem for p in allocations if not (E/p.stem/'receipt.json').exists()]
if set(missing)!={'XRk_L013','XRk_L076'}:errors.append('unexpected missing receipts '+str(missing))
summary={'errors':errors,'allocations':len(allocations),'lean_compiler_invocations':sum(r['kind']=='L' for r in rows),'predecessor_refusals':missing,'kani_runs':sum(r['kind']=='K' for r in rows),'attempts':rows,'accepted_axioms':axioms,'unchanged_top_delta':{'T':0,'P':0,'G':0,'C':0},'baseline_revision':base,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'qualification':'Local model results only; every P6 bridge and actual-top implementation instance remain OPEN.'}
(E/'XRk_Verification.json').write_text(json.dumps(summary,indent=2)+'\n')
for kind in ['L','K']:
 rs=[r for r in rows if r['kind']==kind]
 (E/('XRk_'+('Lean' if kind=='L' else 'Kani')+'Summary.json')).write_text(json.dumps({'used':len(rs),'allocations':len(allocations) if kind=='L' else len(rs),'pass':sum(r['exit']==0 for r in rs),'failed':sum(r['exit']!=0 for r in rs),'wall_seconds':sum(r['wall_seconds'] for r in rs),'peak_rss_kib':max(r['peak_rss_kib'] for r in rs),'swaps':sum(r['swaps'] for r in rs)},indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['errors','allocations','lean_compiler_invocations','predecessor_refusals','kani_runs']}));raise SystemExit(bool(errors))
