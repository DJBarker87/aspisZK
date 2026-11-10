#!/usr/bin/env python3
"""L187 final (a): declaration comparison of EVERY replayed object against the overlay object it replaces.
Runs inside one capped scope. Byte-identical objects are recorded by sha256; every other object is compared
forward (overlay -> replay) and reverse (replay -> overlay) with the runner's L187_Compare binary, in chunks
(one process per chunk; the tool does not free regions)."""
import json,hashlib,pathlib,subprocess,sys
W=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109')
plan=json.loads((W/'l187_plan.json').read_text())['plan']; ov=json.loads((W/'overlay_sha.json').read_text())
out=W/'final'; out.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows={};todo=[]
for m,v in plan.items():
  o=W/'objs'/(v['src_rel'][:-5]+'.olean')
  if not o.is_file(): rows[m]=dict(module=m,replay_object=None); continue
  h=sha(o); rows[m]=dict(module=m,replay_object=str(o),replay_sha256=h,overlay_object=v['overlay'],overlay_sha256=ov.get(m),byte_identical=(h==ov.get(m)))
  if h!=ov.get(m): todo.append(m)
def run(pairs,tag):
  res={}
  for i in range(0,len(pairs),150):
    ch=pairs[i:i+150]; t=out/f'cmp_{tag}_{i}.tsv'; j=out/f'cmp_{tag}_{i}.jsonl'
    t.write_text(''.join(f'{m}\t{a}\t{b}\n' for m,a,b in ch))
    subprocess.run(['timeout','600',str(W/'tools'/'L187_Compare'),str(t),str(j)],check=False)
    for l in j.read_text().splitlines():
      x=json.loads(l); res[x['module']]=x.get('result',x)
    t.unlink(); j.unlink()
  return res
fwd=run([(m,rows[m]['overlay_object'],rows[m]['replay_object']) for m in todo],'fwd')
rev=run([(m,rows[m]['replay_object'],rows[m]['overlay_object']) for m in todo],'rev')
with open(out/'L187_COMPARE_ALL.jsonl','w') as f:
  for m in sorted(rows):
    r=rows[m]
    if m in fwd: r['forward']=fwd[m]; r['reverse']=rev.get(m)
    f.write(json.dumps(r)+'\n')
print('modules',len(rows),'compared',len(todo),'missing_object',sum(1 for r in rows.values() if not r['replay_object']))
