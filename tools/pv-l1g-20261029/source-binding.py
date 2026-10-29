"""Verify unchanged deployed retry/callback source against inherited own-1 binding.
This retains every open native leaf; it does not certify the full native producer.
"""
from pathlib import Path
import hashlib,json,subprocess
E=Path('evidence/pv-l1g-20261029');old=Path('evidence/pv-diag2-20261029/retry-structural-binding.json')
x=json.loads(old.read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();checks=[]
for v in x['source_rows']:
 p=v['path'].split('/src/',1)[1];b=subprocess.check_output(['git','show',rev+':'+p]);checks.append(dict(path=p,revision=rev,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),same_full_file=hashlib.sha256(b).hexdigest()==v['sha256'],same_complete_body=v['body'] in b.decode()))
assert all(v['same_full_file'] and v['same_complete_body'] for v in checks)
f=old.parent/'retry-control-validation.json';assert hashlib.sha256(f.read_bytes()).hexdigest()==x['finite_validation']['sha256']
(E/'retry-source-reuse.json').write_text(json.dumps(dict(source_revision=rev,binding_path=str(old),binding_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),checks=checks,finite_validation_path=str(f),finite_validation_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),classification=x['classification'],scope='Reused own-1 outer retry/callback control binding only; all inherited open leaves remain open.',compiler_boundary=x['compiler_boundary'],open=x['open']),indent=2)+'\n')
