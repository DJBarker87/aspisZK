"""Audit focused receipts and the unchanged actual-top statements."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
entry=json.loads((E/'JFz_ENTRY.json').read_text());attempts=[];accepted={};failures=[]
standard={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('JFz_*/receipt.json')):
 x=json.loads(p.read_text());assert x['kind']=='lean'
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in x['command'];assert x['swaps']=='0'
 for name,h in x['source_hashes'].items():
  assert hashlib.sha256((p.parent/'sources'/name).read_bytes()).hexdigest()==h
 if x['exit_status']==0:
  for line in x['print_axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',line)
   if m:assert set(filter(None,map(str.strip,m[1].split(','))))<=standard,line
  for name,h in x['source_hashes'].items():accepted.setdefault((name,h),[]).append(x['attempt'])
 else:failures.append(x['attempt'])
 attempts.append({'attempt':x['attempt'],'exit_status':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':int(x['peak_rss_kib']),'swaps':x['swaps'],'source_revision':x['source_revision'],'source_hashes':x['source_hashes'],'print_axioms':x['print_axioms'],'receipt':str(p.relative_to(R))})
assert len(attempts)<=100
modules=[]
for p in sorted((R/'lean').glob('JFz_*.lean')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 modules.append({'module':p.stem,'sha256':h,'successful_attempts':accepted.get((p.name,h),[])})
 assert accepted.get((p.name,h)),f'No matching successful compile: {p.name}'
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text()),p
v={'budget':{'lean_max':100,'lean_used':len(attempts),'kani_max':10,'kani_used':0},'passed':len(attempts)-len(failures),'failed_attempts':failures,'maximum_peak_rss_kib':max(x['peak_rss_kib'] for x in attempts),'swaps':0,'axioms':'Only propext, Classical.choice, Quot.sound in successful final results. Failed outputs are rejected.','modules':modules,'attempts':attempts}
(E/'JFz_VALIDATION.json').write_text(json.dumps(v,indent=2)+'\n')
ledger={'method':'PREMISE-LEDGER-20261025.md: quantified atomic-law families; conjunction leaves split and common witnesses, guards, quantifiers and dictionary preserved. Byte-identical before/after statements give an empty row diff.','targets':[],'delta':{'T':0,'P':0,'C':0,'premises_removed':0,'premises_added':0},'nonvacuity':'Full joint accepted source/runtime/frozen3 fixture NOT established; new local forward parsing facts do not count as actual-top premise removals.'}
for name,h in entry['before'].items():
 b=(R/'lean'/f'{name}.lean').read_bytes();after=hashlib.sha256(b).hexdigest();assert h==after
 (E/f'JFz_AFTER_{name}.lean.txt').write_bytes(b)
 ledger['targets'].append({'theorem':f'AspisR1.{name}.deployed','before_sha256':h,'after_sha256':after,'unchanged':True})
(E/'JFz_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({'attempts':len(attempts),'passed':v['passed'],'modules':len(modules),'peak_rss_kib':v['maximum_peak_rss_kib'],'delta':ledger['delta']}))
