from NCJ_host import *
a='NCJ_K064'
r=py(f'''from pathlib import Path
import hashlib,json
b=Path({B!r});removed=[]
for p in (b/'NCJ_tmp').rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
print(json.dumps(dict(lock=hashlib.sha256((b/'NCJ_src/Cargo.lock').read_bytes()).hexdigest(),removed=removed)))
''');assert r.returncode==0
x=json.loads(r.stdout);assert x['lock']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
p=E/(a+'-graph-check.json');g=json.loads(p.read_text());g.update(lock_after_sha256=x['lock'],lock_unchanged=True);p.write_text(json.dumps(g,indent=2)+'\n')
(E/(a+'-solver-cleanup.json')).write_text(json.dumps(x,indent=2)+'\n')
rows=[json.loads(l) for l in (E/'NCJ_ATTEMPTS.jsonl').read_text().splitlines()]
if not any(r['attempt']==a for r in rows):
 with (E/'NCJ_ATTEMPTS.jsonl').open('a') as f:f.write((E/a/'receipt.json').read_text().strip()+'\n')
print('Recovered K064 read-only; lock unchanged; solver temp cleanup complete')
