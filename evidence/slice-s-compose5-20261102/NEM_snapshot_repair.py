"""Remove only redundant recursively named OWN snapshots, validating contents."""
from pathlib import Path
import re,hashlib,json,datetime
E=Path(__file__).resolve().parent
assert not (E/'NEM_ACTIVE.json').exists(),'never repair an active/submitted attempt'
removed=0;total=0;proof=hashlib.sha256();samples=[];bad=[]
for p in E.iterdir():
 if not p.is_file():continue
 m=re.match(r'^((?:NEM_K\d{3}-){2,})(.+CURRENT\.json)$',p.name)
 if not m:continue
 parts=re.findall(r'NEM_K\d{3}-',m[1]);original=E/(parts[-1]+m[2]);data=p.read_bytes()
 if not original.exists() or original.read_bytes()!=data:bad.append(p.name);continue
 h=hashlib.sha256(data).hexdigest();proof.update((p.name+' '+h+'\n').encode());removed+=1;total+=len(data)
 if len(samples)<20:samples.append(dict(removed=p.name,identical_original=original.name,sha256=h))
 p.unlink()
assert not bad,('unmatched duplicate content; retain and inspect',bad[:10])
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='own snapshot glob included previous per-attempt CURRENT snapshots and recursively copied them',removed_duplicates=removed,removed_bytes=total,content_checks='every removed duplicate equals the retained innermost one-level snapshot byte for byte',inventory_sha256=proof.hexdigest(),samples=samples,proof_receipts_deleted=0,no_submitted_job_resubmitted=True,controller='paused then terminated only local NEM_late_campaign.py controller before K087 launch; NEM_ACTIVE absent; K086 receipt complete',fix='only base NEM_[A-Z_]+CURRENT.json names are eligible for snapshot collection; all source/graph/lock/feature/cap gates unchanged')
(E/'NEM_SNAPSHOT_REPAIR.json').write_text(json.dumps(record,indent=1)+'\n')
for name in ['NEM_encoder_remaining_campaign.py','NEM_late_campaign.py']:
 p=E/name;s=p.read_text().replace('import sys,subprocess','import sys,subprocess,re')
 s=s.replace("for p in E.glob('NEM_*CURRENT.json'):(E/(a+'-'+p.name)).write_bytes(p.read_bytes())", "for p in E.glob('NEM_*CURRENT.json'):\n  if re.fullmatch(r'NEM_[A-Z_]+CURRENT\\.json',p.name):(E/(a+'-'+p.name)).write_bytes(p.read_bytes())")
 p.write_text(s)
print(json.dumps({k:record[k] for k in ['removed_duplicates','removed_bytes','proof_receipts_deleted']}))
