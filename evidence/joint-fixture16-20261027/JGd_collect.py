"""Record proof receipts and match final source hashes to successful attempts."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(P.glob('JGd16_*/receipt.json'))]
green={};fail=[]
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 if r['exit_status']==0:
  for x in r['print_axioms']:
   assert 'sorryAx' not in x
   if '[' in x:assert set(re.search(r'\[([^]]*)\]',x).group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'}
  for name,h in r['source_hashes'].items():green[name]={'sha256':h,'attempt':r['attempt'],'axioms':r['print_axioms']}
 else:fail.append({'attempt':r['attempt'],'source_hashes':r['source_hashes'],'exit':r['exit_status'],'errors':(P/r['attempt']/'stdout.log').read_text()})
valid=[];unchecked=[]
for f in sorted((R/'lean').glob('JGd_*.lean')):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',f.read_text()),f
 if f.name not in green or green[f.name]['sha256']!=sha(f):unchecked.append(str(f.relative_to(R)));continue
 valid.append({'source':str(f.relative_to(R)),**green[f.name]})
(P/'JGd_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JGd_FAILURES.json').write_text(json.dumps(fail,indent=2)+'\n')
(P/'JGd_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rs))
summary={'charged_attempts':len(rs),'lean_processes':len(rs),'kani_runs':0,'accepted':sum(r['exit_status']==0 for r in rs),'rejected':len(fail),'final_validated_modules':len(valid),'unchecked_root_modules':unchecked,'total_lean_wall_seconds':sum(r['wall_seconds'] for r in rs),'maximum_reported_peak_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swap':0,'hash_generation_blocks':0,'scope':'focused pinned cache; no package or clean release replay','anomaly':'Attempt090 repeated the ordinary rejected089 source after a generator indentation error; batch was not fail-fast. Charged and excluded. No timeout or memory-killed job was repeated; no cap raised.'}
(P/'JGd_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
if (P/'JGd16_100/stdout.log').exists():
 log=(P/'JGd16_100/stdout.log').read_text()
 for name in ['Rc7_Top.deployed','Rc10_Top.deployed','JGd_Fixture.inhabited','JGd_MaskSource.source','JGd_MaskedGate.retained','JGd_TerminalCriterion.source']:
  start=log.find('theorem AspisR1.'+name+' :');end=log.find("'AspisR1."+name+"' depends on axioms:",start)
  if start>=0 and end>start:(P/f'JGd_AFTER_{name.split(".")[0]}_KERNEL.txt').write_text(log[start:end])
for root in ['Rc7_Top','Rc10_Top']:
 assert (P/f'JGd_BEFORE_{root}.lean.txt').read_bytes()==(P/f'JGd_AFTER_{root}.lean.txt').read_bytes()==(R/'lean'/f'{root}.lean').read_bytes()
for f in P.rglob('*'):
 if f.is_file():assert f.suffix not in ['.olean','.ir','.pyc','.elf','.o','.a','.so','.gz','.tar'],f
print(json.dumps(summary,indent=2))
