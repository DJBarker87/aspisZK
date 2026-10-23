#!/usr/bin/env python3
"""Isolated host objects, capped admission and complete per-attempt receipts."""
import pathlib,json,subprocess,sys,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
TOOLS=ROOT/'tools/ports3-20261023'; E=ROOT/'evidence/ports3-20261023'
HOST='dombarker@100.108.41.90'; REMOTE='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
module=sys.argv[1]; assert module.startswith('Port3_')
source=ROOT/'docs/research/100bit-spend-path-20261013/lean'/f'{module}.lean'
number=1+max((int(p.stem.split('-')[1]) for p in TOOLS.glob('lean-*.json')),default=0); assert number<=100
attempt=f'lean-{number:03d}'
base=ROOT/'docs/research/100bit-spend-path-20261013/evidence/adapter-rw-20261023/lean-048/receipt.json'
inherited=json.loads(base.read_text())
cfg={'attempt':attempt,'kind':'lean','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_tree_dirty':True,'command':['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',f'{module}.olean',f'{module}.lean'],'sources':[f'{module}.lean'],'timeout':180,'env':{'LEAN_PATH':REMOTE+':/home/dombarker/project-offloads/codex-cx-ports1-20261023:/home/dombarker/project-offloads/codex-cx-verifier-top-20261023:'+'/home/dombarker/project-offloads/codex-cx-s2w-20261023:/home/dombarker/project-offloads/codex-cx-s2w-20261023/history-cache:/home/dombarker/project-offloads/codex-cx-s2y-20261023:/home/dombarker/project-offloads/codex-cx-s2y-20261023/parser-cache:/home/dombarker/project-offloads/codex-cx-s2z-20261023:/home/dombarker/project-offloads/codex-cx-s2x-20261023:'+'/home/dombarker/project-offloads/codex-cx-child-joins-20261023:'+inherited['env']['LEAN_PATH']},'deps_fingerprint':{'inherited_receipt_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope':'Selected direct objects pinned; AdapterRw stage3 inherited closure reused'},'expected_time':'Focused cached Lean module, no cold dependency build, generation or elimination'}
cfg['env']['LEAN_PATH'] += ':'+REMOTE+'/retained-cache'
cfg['env']['LEAN_PATH'] += ':/home/dombarker/project-offloads/codex-cx-ports2-20261023:/home/dombarker/project-offloads/codex-cx-ports2-20261023/parser-cache'
c=TOOLS/f'{attempt}.json'
# Reserve before any remote work; an in-flight receipt is not yet present.
with c.open('x') as handle: handle.write(json.dumps(cfg,indent=2)+'\n')
def run(args,**kw):return subprocess.run(args,check=True,**kw)
run(['ssh',HOST,'mkdir','-p',REMOTE])
run(['scp','-q',str(source),str(c),str(TOOLS/'Port3_run_host.py'),str(TOOLS/'Port3_lean_host.py'),HOST+':'+REMOTE+'/'])
# Admission must count populated scopes, not only processes named lean.
admission='''import pathlib,json,sys
base=pathlib.Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service')
rows=[]
for p in base.rglob('*.scope'):
 try:
  if not (p/'cgroup.procs').read_text().strip(): continue
  m=(p/'memory.max').read_text().strip()
  if p.name=='init.scope':continue
  rows.append({'scope':str(p),'max':m,'current':(p/'memory.current').read_text().strip()})
 except FileNotFoundError:pass
assert all(r['max']!='max' for r in rows),rows
reserved=sum(int(r['max']) for r in rows)
print(json.dumps({'scopes':rows,'reserved_bytes':reserved,'additional_bytes':8589934592,'limit_bytes':55*1024**3}))
assert reserved+8589934592<=55*1024**3
'''
r=run(['ssh',HOST,'python3','-c',__import__('shlex').quote(admission)],capture_output=True,text=True)
(E/f'{attempt}-reservation.json').write_text(r.stdout)
cmd=f'cd {REMOTE} && flock /tmp/aspis-r0-lean.lock systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port3_lean_host.py {attempt}.json'
r=subprocess.run(['ssh',HOST,cmd],capture_output=True,text=True)
(E/f'{attempt}-launcher.log').write_text(r.stdout+r.stderr)
run(['scp','-qr',HOST+':'+REMOTE+'/'+attempt,str(E) ])
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
