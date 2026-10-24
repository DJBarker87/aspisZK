"""Collect this continuation's immutable host receipts; count real launches."""
from pathlib import Path
import subprocess,json,hashlib,re
root=Path(__file__).resolve().parents[3]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/effect'
h='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/stage3/'
patterns=['1126[2-9]*','1127*','1128*','out-1126[2-9].log','out-112[78]*.log','time-1126[2-9].log','time-112[78]*.log','sha-1126[2-9].txt','sha-112[78]*.txt']
subprocess.run(['rsync','-a',*[f'--include={p}' for p in patterns],'--exclude=*',f'dombarker@100.108.41.90:{h}',str(e)+'/'],check=True)
for src,dest in [('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json','env-J.json'),('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py','run2.py.txt')]:
 subprocess.run(['scp',f'dombarker@100.108.41.90:{src}',str(e/dest)],check=True,capture_output=True)
env=json.loads((e/'env-J.json').read_text());j='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(e.glob('112*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert a>=11262
 log=(e/f'out-{a}.log').read_text();tm=r['time_log']
 metric=lambda name:int(re.search(re.escape(name)+r':\s*(\d+)',tm)[1])
 wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.*)',tm)[1]
 command=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',j+'/sources','-o',j+'/objects/'+r['module']+'.olean',r['source_path']]
 rows.append(dict(attempt=a,module=r['module'],exit=r['exit_status'],wall=wall,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),source_revision=r['source_revision'],source_sha256=r['source_sha256'],deps_fingerprint=r['deps_fingerprint'],effective_lean_command=command,effective_lean_path=j+'/objects:'+env['LEAN_PATH'],launcher_command=['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/stage3/lean.py',str(a),r['module']],receipt=p.name,full_axioms=r['print_axioms'],accepted=r['exit_status']==0 and 'sorryAx' not in log,limits=r['limits'],reservation_lines=(e/f'{a}-launcher.log').read_text().splitlines()[:2]))
accepted={}
for r in rows:
 if r['accepted']:accepted[r['module']]=r
for module,r in accepted.items():
 p=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],module
summary=dict(schema='prover-rw-effect-focused-evidence-v1',base_revision='7db89a0216818294add9efa77101568aed1a3629',source_revision_note='Base revision plus exact per-attempt uncommitted source/dependency hashes; audit after proof-stage commit records the committed revision.',actual_new_lean_launches=len(rows),stage3_total_lean_used=60+len(rows),stage3_lean_remaining=40-len(rows),kani_used=42,kani_remaining=18,new_kani_runs=0,unlaunched_ids=[dict(attempt=11277,reason='dependency preflight: ProverRwEffectOwner had no olean; no launcher/input/compile'),dict(attempt=11279,reason='short-circuit after 11278 failed; no launch'),dict(attempt=11281,reason='short-circuit after 11280 failed; no launch')],accepted_final={m:r['attempt'] for m,r in accepted.items()},rows=rows,reused='All existing env-J dependencies; source extraction caller-005 and D188 trust boundary; historical runtime/ELF receipts only. No new native identity gate.',blocked='Arbitrary-world native effect adequacy, state threading through native callback/retry, unchanged E1 law and joint experiment transport remain unproved.')
(e/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['actual_new_lean_launches','stage3_total_lean_used','stage3_lean_remaining','accepted_final']},indent=2))
