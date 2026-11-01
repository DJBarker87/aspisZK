"""Read-only focused receipt/source/cache audit. Never launches Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,shlex,time
E=Path('evidence/pv-evh8-20261101')
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(receipts)<=80
attempts=[r['attempt'] for r in receipts]
assert len(set(attempts))==len(attempts)
assert all(79300<=a<=79399 for a in attempts)
prep={sha(p.read_bytes()) for p in list(E.glob('prepare-*.json'))+list((E/'prepare-history').glob('*.json'))}
accepted=[]
for r in receipts:
 a=r['attempt'];src=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])
 assert sha(src)==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r['source_revision']+':'+r['source_path']],text=True).strip()==r['source_git_blob']
 assert r['deps_fingerprint'] in prep,('missing prepare',a)
 out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
 assert f"Exit status: {r['exit']}" in tim
 assert r['wall'] and int(r['peak_rss_kbytes'])<8*1024*1024 and r['swaps']=='0'
 assert r['admission']['allowed'] is True
 assert json.load(open(E/f'transport-{a}.json'))['exit']==int(r['exit'])
 for v in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000']:assert v in r['command']
 if a>=79397:assert r['target'] in ['PV_EVH_ProverAudit','PV_EVH_ProverReplay']
 if r['accepted']:
  assert r['exit']=='0' and 'error:' not in out and 'sorryAx' not in out and r['axioms']
  assert Path(r['source_path']).read_bytes()==src
  for line in r['axioms']:
   if 'depends on axioms:' in line:
    axs=line.split('depends on axioms: [')[1].split(']')[0].replace('\n','').replace(' ','').split(',')
    assert set(axs)<={'propext','Classical.choice','Quot.sound'}
  accepted.append(r)
for short in ['FinishOpening','PublishCompact','NonzeroStep','PrivateSaltStep','PrivateSaltsStep']:
 subprocess.run(['python3','tools/pv-evh8-20261101/open_spine.py',short,'--check'],check=True,capture_output=True)
subprocess.run(['python3','tools/pv-evh8-20261101/nonzero_install.py','--check'],check=True,capture_output=True)
subprocess.run(['python3','tools/pv-evh5-20261029/open_spine.py','PrepareOpening','--check'],check=True,capture_output=True)
for script in ['native_preflight.py','callback_frontier.py','callback_ctor.py']:
 subprocess.run(['python3','tools/pv-evh8-20261101/'+script,'--check'],check=True,capture_output=True)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
code='''import pathlib,hashlib,json,subprocess,time
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-evh-20261029')
print(json.dumps(dict(epoch=time.time(),units=subprocess.check_output(['systemctl','--user','list-units','pv-evh-*','--all','--no-pager'],text=True),files={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in (p/'evidence').iterdir() if q.is_file()},objects={q.stem:hashlib.sha256(q.read_bytes()).hexdigest() for q in (p/'objects').glob('PV_EVH_*.olean')},quiet=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').read_text() if pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists() else None)))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);assert '0 loaded units listed.' in host['units']
for v in receipts:
 a=v['attempt']
 for name in ['admission','out','time']:
  f=f'{name}-{a}.'+('json' if name=='admission' else 'log')
  assert host['files'][f]==sha((E/f).read_bytes()),('host receipt',f)
 if v['accepted']:assert host['objects'][v['target']]==v['object_sha256']
(E/'host-final.json').write_text(json.dumps(host,indent=2)+'\n')
used=set(attempts);fresh=sorted(set(range(79300,79397))-used)
summary=dict(status='PASS focused receipt/source/cache audit; target incomplete',baseline='0da088f6f87a20db01518eb53c95e2343f7b47bf',attempts=len(receipts),passed=len(accepted),failed=len(receipts)-len(accepted),remaining=80-len(receipts),next_fresh_id=fresh[0] if fresh else None,audit_remaining=sorted(set(range(79397,79400))-used),accepted=[dict(target=v['target'],attempt=v['attempt'],wall=v['wall'],peak_rss_kbytes=v['peak_rss_kbytes'],axioms=v['axioms']) for v in accepted],compiler_guard_sha256=sha(Path('tools/pv-evh8-20261101/compile.py').read_bytes()),rows_removed=[],release_replay=False,native=0,kani=0,live_scopes=False)
(E/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='accepted'}))
