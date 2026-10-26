"""Validate receipts, source scope, standard axioms and the mechanical ledger delta."""
from pathlib import Path
import json,re,hashlib,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads((P/f'Rc6_{n:03}'/'receipt.json').read_text()) for n in range(1,101)]
axioms=[]
for r in receipts:
 assert r['exit_status']==0,r['attempt']
 assert r['swaps']=='0',r['attempt']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert len(r['sources'])==1 and r['sources'][0].startswith('Rc6_')
 for src in r['sources']:
  assert sha(R/'lean'/src)==r['source_hashes'][src],(r['attempt'],src)
  assert sha(P/r['attempt']/'sources'/src)==r['source_hashes'][src]
 log=(P/r['attempt']/'stdout.log').read_text()
 assert not re.search(r'\berror(?:\(|:)',log),r['attempt']
 for ax in r['print_axioms']:
  if 'depends on axioms:' in ax:
   names=set(re.search(r'\[([^\]]*)\]',ax)[1].split(', '));assert names<= {'propext','Classical.choice','Quot.sound'},ax
  axioms.append(ax)
 assert r['source_revision'] and r['deps_fingerprint']['selected_objects']
retries={r['attempt']:json.loads((P/(r['attempt']+'-retries.json')).read_text()) for r in receipts}
new=[p for p in (R/'lean').glob('Rc6_*.lean')]
for src in new:
 text=src.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',text,re.M),src
# The proof modules themselves print every declared theorem's axioms.
new_theorems=[]
for src in new:
 text=src.read_text()
 ns=re.search(r'namespace (AspisR1\.Rc6_\w+)',text)
 for m in re.finditer(r'^theorem (\w+)',text,re.M):
  name=m[1];assert '#print axioms '+name in text,(src,name)
  full=ns[1]+'.'+name;assert any("'"+full+"'" in a for a in axioms),full
  new_theorems.append(full)
ledger=R/'design/PREMISE-LEDGER-20261025.md';data=ledger.read_bytes();prefix=json.loads((P/'Rc6_ledger_prefix.json').read_text())
assert sha(ledger) and hashlib.sha256(data[:prefix['bytes']]).hexdigest()==prefix['sha256']
x=json.loads((P/'Rc6_premises.json').read_text());assert x['removed_rows']==['L099','L195','L196','L197','L198','L199']
assert all(r['running_job'] in {'F3X_','SCC_','SAG_','BEf_','JFx_','UNCOVERED'} for r in x['rows'] if r['classification']=='P')
changes=subprocess.check_output(['git','diff','--name-only','e0dbfb6955ac817de347c30978a18e82bfeb4f01'],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
for f in changes+untracked:
 assert f.startswith('lean/Rc6_') or f.startswith('evidence/recount6-20261026/') or f=='design/PREMISE-LEDGER-20261025.md',f
assert not any(f.endswith(('.olean','.ir','.elf','.so','.tar','.gz')) for f in changes+untracked)
summary=dict(lean_attempts=100,successful=100,kani_runs=0,package_replays=0,timeouts=0,memory_kills=0,source_checks=len(new),new_theorems=new_theorems,axiom_reports=len(axioms),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,reservation_retries={k:v for k,v in retries.items() if v},old_ledger_prefix_intact=True,changed_paths=changes,untracked_paths=untracked,no_shipped_changes=True,elf_rebuild_trigger=False,recount=x['counts'])
(P/'Rc6_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'Rc6_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps({k:summary[k] for k in ['lean_attempts','successful','kani_runs','wall_seconds','peak_rss_kib','swaps','axiom_reports','old_ledger_prefix_intact']}))
