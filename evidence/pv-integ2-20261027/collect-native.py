from pathlib import Path
import subprocess,json,hashlib,shlex
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-integ2-20261027'
# Retain only text receipts and hashes; no key, ELF, binary or diagnostic corpus.
code='''from pathlib import Path
import json,hashlib
D=Path(%r);builds=[];keys=[]
for name in ['build-default','build-devnet-retry6','build-pool']:
 P=D/'candidate'/name;c=json.loads((P/'comparison.json').read_text());r=json.loads((P/'receipt/receipt.json').read_text());builds.append(dict(**c,receipt=r))
 for p in (P/'artifacts').glob('*keypair.json'):
  p.chmod(0o600);value=json.loads(p.read_text());keys.append(dict(path=str(p),mode=oct(p.stat().st_mode&0o777),public_key_hex=bytes(value[32:]).hex(),retained=True))
(D/'elf-gate.json').write_text(json.dumps(dict(passed=all(x['matches'] and x['receipt']['exit_status']==0 for x in builds),builds=builds),indent=2)+'\\n')
(D/'key-retention.json').write_text(json.dumps(dict(keys=keys,no_key_cleanup=True,no_transactions=True),indent=2)+'\\n')
'''%D
subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],check=True)
for name in ['elf-gate.json','key-retention.json','cache-reuse.json','cache-inventory.json','all-missing-objects.json','setup-admission.json','setup-reservation.log','formal-setup-admission.json','formal-setup-reservation.log']:
 subprocess.run(['scp','-q',f'{H}:{D}/{name}',str(E/name)],check=True)
for name in ['build-default','build-devnet','build-devnet-retry1','build-devnet-retry3','build-devnet-retry6','build-pool']:
 O=E/'native-receipts'/name;O.mkdir(parents=True,exist_ok=True)
 for f in ['reservation.json','command.json','comparison.json','receipt/receipt.json','receipt/time.log','receipt/stdout.log','receipt/stderr.log']:
  (O/f).parent.mkdir(parents=True,exist_ok=True)
  p=subprocess.run(['scp','-q',f'{H}:{D}/candidate/{name}/{f}',str(O/f)],stderr=subprocess.PIPE,text=True)
  if p.returncode and 'No such file' not in p.stderr:raise RuntimeError(p.stderr)
print('native gate receipts retained')
