"""Read-only receipt/source/object audit. Never a compiler or release replay."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex,time
E=Path('evidence/pv-evh10-20261102');H='/home/dombarker/project-offloads/codex-pv-evh-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
ids=[r['attempt'] for r in rows];assert len(ids)==len(set(ids)) and len(ids)<=100
old=sorted(a for a in ids if a<79500);new=sorted(a for a in ids if a>=79500)
assert old==list(range(79362,79362+len(old))) and len(old)<=18
assert not new or len(old)==18
assert new==list(range(79500,79500+len(new)))
prep={sha(p.read_bytes()) for p in list(E.glob('prepare-*.json'))+list((E/'prepare-history').glob('*.json'))}
accepted=[]
for r in rows:
 a=r['attempt'];raw=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])
 assert sha(raw)==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r['source_revision']+':'+r['source_path']],text=True).strip()==r['source_git_blob']
 assert r['deps_fingerprint'] in prep
 out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
 assert f"Exit status: {r['exit']}" in tim and r['wall']
 assert int(r['peak_rss_kbytes'])<8*1024*1024 and r['swaps']=='0'
 assert json.load(open(E/f'transport-{a}.json'))['exit']==int(r['exit'])
 assert r['admission']['allowed'] is True
 for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000']:assert x in r['command']
 if r['accepted']:
  assert r['exit']=='0' and 'error:' not in out and 'sorryAx' not in out
  assert Path(r['source_path']).read_bytes()==raw
  declarations=re.findall(r'^theorem (\w+)',raw.decode(),re.M)
  assert len(r['axioms'])==len(declarations),(a,'missing axiom print')
  for line in r['axioms']:
   if 'depends on axioms:' in line:
    axs=line.split('depends on axioms: [')[1].split(']')[0].replace('\n','').replace(' ','').split(',')
    assert set(axs)<={'propext','Classical.choice','Quot.sound'}
  accepted.append(r)
# Reproducible read-only source pin checks, no native/extraction execution.
subprocess.run(['python3','tools/pv-evh10-20261102/source_inventory.py','--check'],check=True,capture_output=True)
for script in ['zero_law.py','zero_binding.py','zero_wrappers.py','entropy_iteration.py','callback_inventory.py','raw_source.py','raw_binding.py','raw_history.py']:
 subprocess.run(['python3','tools/pv-evh10-20261102/'+script,'--check'],check=True,capture_output=True)
closure=subprocess.run(['python3','tools/pv-evh8-20261101/native_preflight.py','--check','--require-native-closure'],capture_output=True,text=True)
assert closure.returncode==1
code='''from pathlib import Path
import hashlib,json,subprocess,time
p=Path('/home/dombarker/project-offloads/codex-pv-evh-20261029')
q=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
print(json.dumps(dict(epoch=time.time(),units=subprocess.check_output(['systemctl','--user','list-units','pv-evh-*','--all','--no-pager'],text=True),quiet=q.read_text() if q.exists() else None,files={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in (p/'evidence').iterdir() if f.is_file()},objects={f.stem:hashlib.sha256(f.read_bytes()).hexdigest() for f in (p/'objects').glob('PV_EVH_*.olean')})))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);assert '0 loaded units listed.' in host['units']
for v in rows:
 a=v['attempt']
 for n in ['admission','out','time']:
  name=f'{n}-{a}.'+('json' if n=='admission' else 'log')
  assert host['files'][name]==sha((E/name).read_bytes())
 if v['accepted']:assert host['objects'][v['target']]==v['object_sha256']
(E/'host-final.json').write_text(json.dumps(host,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
summary=dict(status='PASS focused evidence only; native task incomplete',baseline='d88f951fd4725367ea93b58fb09f8ddc37856ca4',attempts=len(rows),accepted=len(accepted),failed=len(rows)-len(accepted),remaining=100-len(rows),inherited_remaining=18-len(old),next_fresh=79362+len(old) if len(old)<18 else 79500+len(new),audits_untouched=[79397,79398,79399,79597,79598,79599],rows_removed=[],native=0,kani=0,release_replay=False,live_scopes=False,guard_sha256=sha(Path('tools/pv-evh10-20261102/compile.py').read_bytes()))
(E/'validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
