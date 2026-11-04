from NEW_remote import *
import hashlib
assert not(E/'NEW_ACTIVE.json').exists()
a='NEW_K087_CLEANUP';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
root=Path({B!r})/'NEW_tmp';removed=[]
for p in root.rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
print(json.dumps(dict(owned_tmpdir=str(root),removed=removed,shared_tmp_untouched=True)))
''');assert r.returncode==0,r.stderr
(E/'NEW_K087_CLEANUP.json').write_text(r.stdout)
