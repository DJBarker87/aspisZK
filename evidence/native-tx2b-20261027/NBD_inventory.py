from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
p=json.loads(Path('evidence/native-inv2-20261027/NBI2_INVENTORY.json').read_text())
rev=p['source_revision']; rows=[]
for f in p['functions']:
 if f['bridge_unit'] not in ['U03','U04','U05']:continue
 data=subprocess.check_output(['git','show',rev+':'+f['file']]);body=data[f['body_start_byte']:f['body_end_byte']]
 assert hashlib.sha256(data).hexdigest()==f['file_sha256']
 assert hashlib.sha256(body).hexdigest()==f['body_sha256']
 rows.append(f)
q=dict(source_revision=rev,worktree_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),members=rows,
 counts={u:sum(f['bridge_unit']==u for f in rows) for u in ['U03','U04','U05']},
 validation='Exact frozen file and body hashes checked; no native/refinement result claimed')
(E/'NBD_MEMBERS.json').write_text(json.dumps(q,indent=2)+'\n')
print(q['counts'])
