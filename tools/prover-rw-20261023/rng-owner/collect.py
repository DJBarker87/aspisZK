from pathlib import Path
import subprocess,json,re,hashlib,shutil
R=Path(__file__).resolve().parents[3];E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-owner'
H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';T=R/'tools/prover-rw-20261023/rng-preflight'
subprocess.run(['rsync','-a','--exclude=*.olean',f'dombarker@100.108.41.90:{H}/rng-owner/',str(E)+'/'],check=True)
for name in ['rng-owner-extract-001','rng-owner-extract-002','rng-owner-aeneas-001']:
 subprocess.run(['rsync','-a','--exclude=inputs',f'dombarker@100.108.41.90:{H}/src/receipts/{name}/',str(E/name)+'/'],check=True)
p=E/'rng-owner-extract-001';time=(p/'time.log').read_text();pre=json.loads((p/'preflight.json').read_text())
(p/'recovered-receipt.json').write_text(json.dumps(dict(schema='rng-owner-recovered-translation-failure-v1',target=pre['target'],exit_status=int(re.search(r'Exit status: (\d+)',time)[1]),time_log=time,source_revision=pre['source_revision'],source_sha256=pre['source_sha256'],limits=pre['limits'],print_axioms='N/A translation process',wrapper_error='receipt finalization could not locate rustc; Charon had already failed because PATH lacked rustup; native compilation never started',rerun_change='explicit PATH including /home/dombarker/.cargo/bin passed inside new independently capped scope; no cap increase'),indent=2)+'\n')
env=json.loads((E/'env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];log=(E/f'out-{a}.log').read_text()
 assert 11400<=a<=11499
 r['accepted']=r['exit_status']==0 and 'sorryAx' not in log
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 r['receipt_path']=str(p.relative_to(R));r['time_path']=str((E/f'time-{a}.log').relative_to(R))
 r['raw_log_sha256']=hashlib.sha256(log.encode()).hexdigest()
 # Per-attempt JSON already retains exact dependencies and full #print axioms.
 rows.append({k:r[k] for k in ['attempt','module','source_revision','source_sha256','deps_fingerprint','exit_status','accepted','receipt_path','time_path','raw_log_sha256','print_axioms','effective_lean_command','effective_lean_path']})
assert len(rows)<=60
summary=dict(schema='rng-owner-evidence-v1',base='ece5baabbc9c975d631aae8d5ca716e28ad4f268',branch='codex/cx-prover-rw-20261023',ledgers=dict(exhausted_stage3=dict(lean_used=100,lean_limit=100),new_owner_stage=dict(lean_used=len(rows),lean_limit=60,lean_remaining=60-len(rows)),cumulative=dict(lean_used=100+len(rows),lean_authorized=160,kani_used=44,kani_original_limit=60,kani_new_runs=0,kani_remaining=16)),attempts=rows,new_validation='default-option normalization four-module closure; new transparent borrowed owner emission; symbolic source step, checked cap16 induction, same-state replay, exact event/order/count/suffix certificate',reused='preflight source-derived owned emission, pinned Charon/Aeneas/runtime primitives, unchanged 26214-case local differential and single-iteration Kani evidence with original limits; neither runtime nor Kani rerun, neither used as a Lean axiom',scope='isolated prototypes and new ProverRwRngOwner* modules only; no crates/programs change; candidate unadopted',source_assessment='host source-revision labels remain historical; exact prototype source hash and LLBC embedded source, complete declaration signatures/spans, common-declaration normalization and git source commits establish this packet source; older ELF evidence is not a new identity gate',native_remaining=['getrandom::Error layout/E1 association','physical zeroization/drop','actual selected callback/cap8 state producer','ledger/error/world/refinement/joint L1/L2 laws','native artifact/runtime/performance gates'],final_proof_source_revision='ad9e91a840067eae7a44e8ab7f103b0e59b24698',limits='Lean existing5G/7G no swap Tasks64; Rust/extraction6G/8G no swap Tasks64; independently reserved <55GiB; existing launcher timing/lock rules; no cap increases, no memory-pressure failures',full_frozen_manifest_ran=False)
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>5_000_000:raise RuntimeError(('large derived artifact must be hash+size only',str(p)))
print(json.dumps(summary['ledgers']))
