from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
rs=[];passing={};printed=[]
for f in sorted(P.glob('ARX_*/receipt.json')):
 r=json.loads(f.read_text());rs.append(r)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and '-M7000' in r['command']
 assert not re.search(r'timed out|excessive memory consumption', (f.parent/'stdout.log').read_text(),re.I)
 for name,h in r['source_hashes'].items():assert sha(f.parent/'sources'/name)==h
 if not r['exit_status']:
  for l in r['print_axioms']:
   m=re.search(r'axioms: \[(.*)\]',l)
   assert ('does not depend on any axioms' in l) or (m and set(m.group(1).split(', '))<=allowed),l
   printed.append(l)
  for name,h in r['source_hashes'].items():passing[(name,h)]=r['attempt']
assert len(rs)<=100
current=[]
for f in sorted((R/'lean').glob('ARX_*.lean')):
 assert (f.name,sha(f)) in passing,(f,'no current passing receipt')
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',f.read_text(),re.M)
 for name in re.findall(r'^theorem (\w+)',f.read_text(),re.M):
  assert any("'AspisR1."+f.stem+'.'+name+"'" in l for l in printed),name
 current.append({'path':str(f.relative_to(R)),'sha256':sha(f),'passing_attempt':passing[(f.name,sha(f))]})
before=(P/'ARX_BEFORE_STATEMENT.lean.txt').read_text();after=(P/'ARX_AFTER_STATEMENT.lean.txt').read_text()
assert before[before.index('    let select :'):]==after[after.index('    let select :'):]
for forbidden in ['(runtime : F3T_Runtime.Runtime)','(binding :','(P : F3T_ByteCarrier.ByteProver)','(support :','(numeric :']:
 assert forbidden not in after,forbidden
assert 'ARW_Induced.issued' in after and 'ARX_AdmittedRuntime.runtime' in after
x=json.loads((P/'ARX_LEDGER_DELTA.json').read_text())
assert sha(R/'lean/Rc10_Top.lean')==x['source_before_sha256']
assert sha(R/'lean/ARX_Root.lean')==x['source_after_sha256']
assert x['removed']==['L159','L181'] and x['removed_aliases']==['L185']
for scope in ['actual antecedent','deployment only','deployment alias']:
 for key,rows in [('before',x['rows']),('after',x['candidate_rows'])]:
  rows=[r for r in rows if r['scope']==scope]
  assert x[key][scope]=={'rows':len(rows),'classes':{c:sum(r['classification']==c for r in rows) for c in 'TPGC'}}
assert x['actual_adopted_after']==x['before']
paths=subprocess.check_output(['git','diff','--name-only','29ae49d040'],cwd=R,text=True).splitlines()
assert all(p.startswith(('lean/ARX_','evidence/account-rejoin9-20261026/')) for p in paths)
assert all(not p.endswith(('.olean','.elf','.tar','.tar.gz')) for p in paths)
if '--final' in sys.argv:assert len(rs)==100
summary={'status':'pass','scope':'Proposed admitted model theorem, focused cached validation only; no adoption or release rebuild',
 'lean_attempts':len(rs),'passed':sum(not r['exit_status'] for r in rs),'excluded_development_failures':[r['attempt'] for r in rs if r['exit_status']],
 'kani_runs':0,'wall_seconds':sum(r['wall_seconds'] for r in rs),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swaps':sum(int(r['swaps']) for r in rs),
 'current_sources':current,'proposed_removed':['L159','L181'],'removed_aliases':['L185'],'actual_adopted_delta':0,
 'remaining_lean_budget':100-len(rs),'nonvacuity':'Conditional on the same-installation complete real-byte native pair; exact partial predecessors listed in root comparison',
 'conservativity':'Unconditional admitted-runtime counterpart; literal unfiltered ARW_OldRoot instantiation is not asserted'}
(P/'ARX_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'ARX_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
print(json.dumps({k:v for k,v in summary.items() if k!='current_sources'}))
