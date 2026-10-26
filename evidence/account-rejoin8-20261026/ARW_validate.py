from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];passing={};printed=[]
for f in sorted(P.glob('ARW_*/receipt.json')):
 r=json.loads(f.read_text());receipts.append(r)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 assert '-M7000' in r['command']
 for name,h in r['source_hashes'].items():
  snap=f.parent/'sources'/name
  assert hashlib.sha256(snap.read_bytes()).hexdigest()==h
 if r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[(.*)\]',line)
   assert m and set(m.group(1).split(', '))<=allowed,line
   printed.append(line)
  for name,h in r['source_hashes'].items():passing[(name,h)]=r['attempt']
assert len(receipts)<=100
current=[]
for f in sorted((R/'lean').glob('ARW_*.lean')):
 h=hashlib.sha256(f.read_bytes()).hexdigest()
 assert (f.name,h) in passing,f'{f}: no passing receipt for current bytes'
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',f.read_text(),re.M)
 for name in re.findall(r'^theorem (\w+)',f.read_text(),re.M):
  assert any("'AspisR1."+f.stem+'.'+name+"'" in line for line in printed),name
 current.append({'path':str(f.relative_to(R)),'sha256':h,'passing_attempt':passing[(f.name,h)]})
before=(P/'ARW_BEFORE_STATEMENT.lean.txt').read_text();actual=(P/'ARW_AFTER_ACTUAL_STATEMENT.lean.txt').read_text();requested=(P/'ARW_REQUESTED_STATEMENT.lean.txt').read_text()
assert before==actual
assert before[before.index('    let select :'):]==requested[requested.index('    let select :'):]
assert '(runtime : F3T_Runtime.Runtime)' not in requested and '(binding :' not in requested
assert '(P : F3T_ByteCarrier.ByteProver)' not in requested
assert 'let P := ARW_Induced.program' in requested
assert 'ARU_Support.At' not in requested and 'ARU_AllWorld.Supported' not in requested
ledger=json.loads((P/'ARW_LEDGER_DELTA.json').read_text())
assert ledger['before']==ledger['after'] and not ledger['removed'] and ledger['aliases']=={'L185':'L159'}
assert hashlib.sha256((R/'lean/Rc10_Top.lean').read_bytes()).hexdigest()==ledger['source_before_sha256']
for scope in ['actual antecedent','deployment only','deployment alias']:
 rows=[r for r in ledger['rows'] if r['scope']==scope]
 assert ledger['before'][scope]['classes']=={c:sum(r['classification']==c for r in rows) for c in 'TPGC'}
paths=subprocess.check_output(['git','diff','--name-only','ffe1d04316aaca07f13d63d0074e82e2c2c25ed1'],cwd=R,text=True).splitlines()
assert all(x.startswith(('lean/ARW_','evidence/account-rejoin8-20261026/')) for x in paths)
assert all(not x.endswith(('.olean','.elf','.tar','.tar.gz')) for x in paths)
summary={'status':'pass','scope':'Offline focused evidence/source/axiom/ledger validation; no release build or proof of Requested','lean_attempts':len(receipts),'passed':sum(r['exit_status']==0 for r in receipts),'failed':[r['attempt'] for r in receipts if r['exit_status']],'kani_runs':0,'wall_seconds':sum(r['wall_seconds'] for r in receipts),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':sum(int(r['swaps']) for r in receipts),'current_sources':current,'actual_removed_rows':[],'remaining_lean_budget':100-len(receipts),'stop_reason':'Required admitted-domain inference refuted for the literal runtime; scope clarification pending, no numerical root refutation or budget exhaustion claimed.'}
(P/'ARW_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'ARW_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps({k:v for k,v in summary.items() if k!='current_sources'}))
