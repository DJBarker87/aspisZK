from pathlib import Path
import json,subprocess,hashlib,re
D=Path(__file__).resolve().parent;R=D.parents[2];H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023'
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-caller';E.mkdir(exist_ok=True)
subprocess.run(['rsync','-a','--exclude=*.olean',f'dombarker@100.108.41.90:{H}/rng-caller/',str(E)+'/'],check=True)
for kind,ids in [('extract',range(1,5)),('aeneas',range(1,5)),('runtime',range(1,3))]:
 for i in ids:
  name=f'rng-caller-{kind}-{i:03}';(E/name).mkdir(exist_ok=True)
  subprocess.run(['rsync','-a',f'dombarker@100.108.41.90:{H}/src/receipts/{name}/',str(E/name)+'/'],check=True)
subprocess.run(['rsync','-a',f'dombarker@100.108.41.90:{H}/src/reservation-rng-caller-*',str(E)+'/'],check=True)
subprocess.run(['scp','dombarker@100.108.41.90:/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json',str(E/'env-J.json')],check=True,capture_output=True)
subprocess.run(['scp','dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(E/'run2.py.txt')],check=True,capture_output=True)
env=json.loads((E/'env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 11440<=a<=11459
 r['source_revision_full']=subprocess.run(['git','rev-parse',r['source_revision']],cwd=R,capture_output=True,text=True,check=True).stdout.strip()
 r['revision_assessment']='11440-11458 record parent revision plus immutable work-in-progress source/dependency snapshots; 11459 is final committed proof source'
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 (E/f'{a}-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 log=(E/f'out-{a}.log').read_text();r['accepted']=r['exit_status']==0 and 'sorryAx' not in log
 rows.append(r)
summary=dict(schema='rng-caller-preflight-v1',base='03444c5e5e',final_proof_source_revision=subprocess.run(['git','rev-parse','f3e9539784'],cwd=R,capture_output=True,text=True,check=True).stdout.strip(),ledgers=dict(stage3_used=100,stage3_limit=100,owner_previous_used=40,caller_used=len(rows),owner_total_used=40+len(rows),owner_limit=60,lean_remaining=20-len(rows),cumulative_used=140+len(rows),cumulative_limit=160,kani_used=44,kani_limit=60,kani_remaining=16,kani_new=0),attempts=[{k:r[k] for k in ['attempt','module','source_revision','source_sha256','deps_fingerprint','exit_status','accepted','print_axioms','limits']} for r in rows],source_assessment='Exact prototype source equals final LLBC embedded lib.rs; local native source hashes/spans and all substitutions in source-map.json. Host native source-revision labels are historical, not new native identity evidence. Prototype uses getrandom0.3.4 matching native lock; zeroize1.9.1 reuses accepted predecessor while native lock1.8.1 remains unassociated. No crates/programs changes.',established=['emitted From preserves arbitrary parameter-carrier error and selected map_err produces Entropy','concrete emitted guard/error/rejected/success transitions preserve advanced owned state','complete sound cap8 replay with at most8 callbacks and ordered indices','callback admitted execution decomposes into exactly one actual FnMut invocation then exact entropy invocation','concrete zero-block rejection then successful entropy, body rejection, next successful entropy and fatal Semantic composition'],boundaries=['NativeTypes core NonZero niche representation is uninstalled; Aeneas TPattern rejection retained','owned-store Body interface does not prove native prove_masked_attempt/reservation/status/event semantics; audit u64 is placeholder','physical drop/cleanup and native Zeroizing1.8.1 association open','universal cap16 carrier transport and general cap8 entropy draw inventory not proved; prior u8 certificate not silently instantiated','native successful bytes/context -> existing Raw/E1 event transport not proved; E1 unchanged','no native E1/E2/L1/L2, ELF/performance, full-manifest, adoption, merge or push'],validation_reused='accepted cap16 proof and extraction/runtime policy at original boundary; reused nonzero scan theorem through checked scan_same. No unchanged cap16 audit/test rerun.',validation_new='four Charon, four Aeneas attempts including one precise failed niche translation; stateful optimized tests in embedded and separated fixtures; all Lean attempts retained',limits='Lean5G/7G zero swap Tasks64, Rust6G/8G zero swap Tasks64; reservation checks under55GiB. Parallel/window/global-lock launcher unchanged. No cap increase or resource failure.',target='not yet established')
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>5_000_000:
  (p.with_suffix(p.suffix+'.hash.json')).write_text(json.dumps(dict(path=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))+'\n');p.unlink()
print(json.dumps(summary['ledgers']))
