"""Collect exact task receipts, preserve failures, and validate final JGb sources."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(P.glob('JGb15_*/receipt.json'))]
preflight=[]
for n,reason in [(18,'launcher direct-import lookup: FileNotFoundError: PoseidonPreparedSum3Source'),(28,'scp namespace directory absent; no Lean launched')]:
 preflight.append(dict(attempt=f'JGb15_{n:03}',kind='pre-Lean staging/launcher failure',reason=reason,lean_launched=False,exit_status=1,wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms=None,source_config=json.loads((P/f'JGb15_{n:03}.json').read_text())))
(P/'JGb_PREFLIGHT_FAILURES.json').write_text(json.dumps(preflight,indent=2)+'\n')
assert len(rs)==98
assert {r['attempt'] for r in rs}|{x['attempt'] for x in preflight}=={f'JGb15_{i:03}' for i in range(1,101)}
green={};bad=[]
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 if r['exit_status']==0:
  assert all('sorryAx' not in x for x in r['print_axioms'])
  for name,h in r['source_hashes'].items():green[name]={'sha256':h,'attempt':r['attempt'],'axioms':r['print_axioms']}
 else:bad.append({'attempt':r['attempt'],'sources':r['sources'],'exit':r['exit_status'],'errors':(P/r['attempt']/'stdout.log').read_text()})
valid=[]
for f in sorted((R/'lean').glob('JGb_*.lean')):
 assert f.name in green and green[f.name]['sha256']==sha(f),f
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',f.read_text()),f
 valid.append({'source':str(f.relative_to(R)),**green[f.name]})
(P/'JGb_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JGb_FAILURES.json').write_text(json.dumps(bad,indent=2)+'\n')
with (P/'JGb_ATTEMPTS.jsonl').open('w') as o:
 for r in rs:o.write(json.dumps(r,sort_keys=True)+'\n')
summary={'charged_attempts':100,'lean_processes':98,'pre_lean_failures':2,'kani_runs':0,'accepted':sum(r['exit_status']==0 for r in rs),'rejected_lean':len(bad),'final_validated_modules':len(valid),'unchanged_dependency_builds':43,'total_lean_wall_seconds':sum(r['wall_seconds'] for r in rs),'maximum_reported_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swap':0,'hash_generation_blocks':0,'final_receipt':rs[-1],'scope':'focused cached compilation; no package/clean release replay'}
(P/'JGb_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
log=(P/'JGb15_100/stdout.log').read_text()
for name in ['Rc7_Top.deployed','Rc10_Top.deployed','JGb_FoldFixture.inhabited','JGb_Fixture.inhabited']:
 start=log.find('theorem AspisR1.'+name+' :')
 if start>=0:
  end=log.find("'AspisR1."+name+"' depends on axioms:",start)
  assert end>start
  (P/f'JGb_AFTER_{name.split(".")[0]}_KERNEL.txt').write_text(log[start:end])
for root in ['Rc7_Top','Rc10_Top']:
 assert (P/f'JGb_BEFORE_{root}.lean.txt').read_bytes()==(P/f'JGb_AFTER_{root}.lean.txt').read_bytes()==(R/'lean'/f'{root}.lean').read_bytes()
for f in P.rglob('*'):
 if f.is_file():assert f.suffix not in ['.olean','.ir','.pyc','.elf','.o','.a','.so','.gz','.tar'],f
(P/'JGb_STATIC_CHECKS.json').write_text(json.dumps({'validated_current_sources':len(valid),'unchecked_root_lean_modules':[],'standard_axioms_only':True,'before_after_top_source_statements_identical':True,'shipped_source_changes':False,'binary_artifacts':[]},indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='final_receipt'},indent=2))
