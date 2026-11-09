#!/usr/bin/env python3
"""Stage 1 of the closure-wide stale-import check: parse every successful committed receipt that
compiled a closure project module (from git grep), keeping -o output, workspace, LEAN_PATH roots
and pinned dependency objects."""
import json,subprocess,sys,os
os.chdir('/Users/dominic/ZK/.worktrees/cx-integrate')
S='/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/'
P=json.load(open(S+'l187_plan.json'))['plan']
rel2m={m.replace('.','/')+'.olean':m for m in P}
files=[l.split(':',1)[1].strip() for l in open(S+'all_receipts_raw.txt') if l.strip()]
pr=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
import threading
threading.Thread(target=lambda:(pr.stdin.write(''.join('HEAD:'+f+'\n' for f in files).encode()),pr.stdin.close())).start()
out=[]
for f in files:
  h=pr.stdout.readline().split(); n=int(h[2]); d=pr.stdout.read(n); pr.stdout.read(1)
  try: r=json.loads(d)
  except Exception: continue
  c=r.get('command') or []
  if r.get('exit_status')!=0 or '-o' not in c: continue
  o=c[c.index('-o')+1]
  m=None
  for i in range(len(o)):
    if (i==0 or o[i-1]=='/') and o[i:] in rel2m: m=rel2m[o[i:]]; break
  if not m: continue
  env=r.get('env') or {}
  base=os.path.dirname(env['TMPDIR']) if env.get('TMPDIR') else None
  df=r.get('deps_fingerprint'); so=(df.get('selected_objects') if isinstance(df,dict) else None) or {}
  pins={v['path']:v['sha256'] for v in (so.values() if isinstance(so,dict) else []) if isinstance(v,dict) and str(v.get('path','')).endswith('.olean') and 'sha256' in v}
  out.append(dict(module=m,file=f,attempt=r.get('attempt'),out=o,base=base,lean_path=(env.get('LEAN_PATH') or '').split(':'),pins=pins,source_hashes=r.get('source_hashes')))
pr.wait()
json.dump(out,open(S+'stale_stage1.json','w'))
import collections
print(len(files),'receipt files;',len(out),'successful module compiles;',len({x['module'] for x in out}),'modules;',sum(1 for x in out if x['pins']),'with pins')
