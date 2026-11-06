from pathlib import Path
import subprocess,json,base64,lzma,hashlib,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108';a=sys.argv[1]
assert not (E/a).exists(),'Existing local receipt; do not duplicate'
code="""from pathlib import Path
import json,base64
b=Path(B);p=b/a
assert (p/'receipt.json').is_file(),'No receipt; never resubmit'
print(json.dumps({str(q.relative_to(b)):base64.b64encode(q.read_bytes()).decode() for q in p.rglob('*') if q.is_file()}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\na='+repr(a)+'\n'+code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for name,encoded in json.loads(r.stdout).items():
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(encoded)
 if len(raw)>1000000 and p.suffix!='.xz':p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k not in ['deps_fingerprint','env']};entry.update(full_receipt=a+'/receipt.json',recovered_read_only=True)
assert not any(json.loads(l)['attempt']==a for l in(E/'NKG_ATTEMPTS.jsonl').read_text().splitlines())
with(E/'NKG_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
