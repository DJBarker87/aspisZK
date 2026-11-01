"""Receipt/source audit only; no compiler or release regression is launched."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,shlex,time
E=Path('evidence/pv-evh5-20261029');old=Path('evidence/pv-evh4-20261029')
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
focused=[v['attempt'] for v in receipts if v['attempt']<73697]
assert focused==list(range(73623,max(focused)+1))
assert all(v['attempt']<73697 or v['attempt']==73699 for v in receipts)
next_fresh=max(focused)+1
prep={sha(p.read_bytes()):str(p) for p in list(E.glob('prepare-*.json'))+list((E/'prepare-history').glob('*.json'))}
# The first historical staging snapshot predates prepare-history support.
for commit in subprocess.check_output(['git','log','--format=%H','841ae0f9a9..HEAD'],text=True).splitlines():
 try: raw=subprocess.check_output(['git','show',commit+':'+str(E/'prepare-PV_EVH_RetryBody.json')],stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:continue
 prep[sha(raw)]=commit+':'+str(E/'prepare-PV_EVH_RetryBody.json')
accepted=[]
for r in receipts:
 a=r['attempt'];src=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])
 assert sha(src)==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r['source_revision']+':'+r['source_path']],text=True).strip()==r['source_git_blob']
 assert r['deps_fingerprint'] in prep,('missing prepare snapshot',a)
 text=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
 assert f"Exit status: {r['exit']}" in tim and r['wall'] and int(r['peak_rss_kbytes'])<8*1024*1024 and r['swaps']=='0'
 assert r['admission']['allowed'] is True
 assert json.load(open(E/f'transport-{a}.json'))['exit']==int(r['exit'])
 cmd=r['command'];assert '-p' in cmd
 for item in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000']:assert item in cmd
 if r['accepted']:
  assert r['exit']=='0' and 'error:' not in text and 'sorryAx' not in text and r['axioms']
  assert Path(r['source_path']).read_bytes()==src
  for v in r['axioms']:
   if 'depends on axioms:' in v:
    axioms=v.split('depends on axioms: [')[1].split(']')[0].replace('\n','').replace(' ','').split(',')
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
  accepted.append(dict(attempt=a,target=r['target'],wall=r['wall'],peak_rss_kbytes=r['peak_rss_kbytes'],axioms=r['axioms']))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
for p in Path('tools/pv-evh5-20261029').glob('*.py'):ast.parse(p.read_text())
subprocess.run(['python3','tools/pv-evh5-20261029/retry.py','--check'],check=True)
subprocess.run(['python3','tools/pv-evh5-20261029/prefix_retry.py','--check'],check=True)
for cmd in [['masked.py','--check'],['open_spine.py','MaskedWithAttempt','--check'],['open_spine.py','ReserveBuild','--check'],['open_spine.py','DurableReserveBuild','--check'],['reserve_join.py','--check'],['account_guard.py','--check']]:
 subprocess.run(['python3','tools/pv-evh5-20261029/'+cmd[0]]+cmd[1:],check=True)
for short in ['DurableWithAttempt','EntropyStep','NoncePath','MaterialFromEntropy','ApplyMaterial','BuildSemantics','ProveSemantics','PrivateSalts','SyncDirectory','NonceReserveFallible','NonceReserve']:
 subprocess.run(['python3','tools/pv-evh5-20261029/open_spine.py',short,'--check'],check=True)
for mode in ['AccountFlow','AccountFlowEntry']:
 subprocess.run(['python3','tools/pv-evh5-20261029/entropy_entry.py',mode,'--check'],check=True)
for script in ['durable_flow.py','nonce_build.py']:
 subprocess.run(['python3','tools/pv-evh5-20261029/'+script,'--check'],check=True)
code='''import pathlib,hashlib,json,subprocess,time
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-evh-20261029')
print(json.dumps(dict(epoch=time.time(),units=subprocess.check_output(['systemctl','--user','list-units','pv-evh-*','--all','--no-pager'],text=True),files={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in (p/'evidence').iterdir() if q.is_file()},objects={q.stem:hashlib.sha256(q.read_bytes()).hexdigest() for q in (p/'objects').glob('PV_EVH_*.olean')},quiet=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').read_text() if pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists() else None)))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);(E/'host-final.json').write_text(json.dumps(host,indent=2)+'\n')
assert '0 loaded units listed.' in host['units']
for v in receipts:
 a=v['attempt']
 for name in ['admission','out','time']:
  f=f'{name}-{a}.'+('json' if name=='admission' else 'log')
  assert host['files'][f]==sha((E/f).read_bytes())
 if v['accepted']:assert host['objects'][v['target']]==v['object_sha256']
summary=dict(status='PASS receipt and source audit; incomplete proof frontier',baseline='841ae0f9a98c89a780803664aaf8755f48343b53',new_attempts=len(receipts),new_passed=len(accepted),new_failed=len(receipts)-len(accepted),cumulative_spent=17+len(receipts),remaining=83-len(receipts),next_fresh_id=next_fresh,audit_remaining=[73699],accepted=accepted,guard_sha256=sha(Path('tools/pv-evh5-20261029/compile.py').read_bytes()),native=0,kani=0,rows_removed=[],release_replay=False,live_scopes=False)
(E/'validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
