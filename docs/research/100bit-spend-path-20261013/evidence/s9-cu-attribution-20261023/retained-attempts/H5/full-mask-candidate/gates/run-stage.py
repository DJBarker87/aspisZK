from pathlib import Path
import hashlib, json, os, re, subprocess, time

W = Path(__file__).resolve().parent
RUN = W.parent
G = 1024**3
CG = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits = {k: (CG/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits == {'memory.high':str(512*1024**2),'memory.max':str(G),'memory.swap.max':'0'}, limits
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
artifact = RUN/'artifacts/aspis_r1_cost_probe_program.so'
proof = Path('/home/dombarker/project-offloads/s4-combined-candidate-20261021/full-osmask-pool-control-v3/tasks/frozen-default/proof.bin')
public = Path('/home/dombarker/project-offloads/s4-combined-candidate-20261021/full-osmask-pool-control-v3/tasks/frozen-default/public.bin')
pool = Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/artifacts/pool/aspis_pool.so')
registry = Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')
driver = Path('/home/dombarker/project-offloads/codex-cx-cu-bound3-20261020/driver-target/release/pool_gate_osmask')
expected = {
    'candidate': 'b5cb382b1738a016b2463d2388fd38523e55577bf8053b7b4f68aee482fa4d5b',
    'proof': '42fc1617dbc212ef07f7a5cd4f177d2014530198a2fefa40d25914d79ca46ee8',
    'public': '5b3b4ea275b0f447bdfc69a726b6e42f20d40c54af414feb1832a6a4174c9410',
}
assert all(x.is_file() for x in [artifact,proof,public,pool,registry,driver])
actual={k:sha(v) for k,v in [('candidate',artifact),('proof',proof),('public',public)]}
assert actual==expected, actual
out=RUN/'result/evidence.json';out.parent.mkdir(parents=True,exist_ok=False)
cmd=[str(driver),str(pool),str(artifact),str(registry),str(out),str(RUN/'result/task'),
     'transfer','success','--pairs','0','--seed','20001','--split','10','--uniform-lane',
     '--tx-version','v1','--zeroed-genesis-page','--reuse',str(proof),str(public)]
inputs={'driver_sha256':sha(driver),'pool_elf_sha256':sha(pool),'candidate_elf_sha256':sha(artifact),
        'registry_elf_sha256':sha(registry),'proof_sha256':sha(proof),'public_sha256':sha(public)}
(W/'command.json').write_text(json.dumps({'argv':cmd,'cwd':'/home/dombarker/project-offloads/codex-cx-pin-20261020',
    'fixture_seed':20001,'source_mask_mode':'os (from original corpus provenance; reused exact proof)',
    'mask_layout':'full-mask','input_hashes':inputs,'timeout_seconds':120},indent=2)+'\n')
before=(CG/'memory.events').read_text(); start=time.monotonic();env=dict(os.environ)
env['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin:/usr/bin:/bin'
with (W/'output.log').open('x') as log:
    result=subprocess.run(['/usr/bin/time','-v','-o',str(W/'time.log'),*cmd],cwd='/home/dombarker/project-offloads/codex-cx-pin-20261020',env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
timing=(W/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
receipt={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),
    'peak_process_rss_kib':int(m[1]) if m else None,'scope_peak_bytes':int((CG/'memory.peak').read_text()),
    'swap_current_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,
    'memory_events_after':(CG/'memory.events').read_text(),'limits':limits,
    'candidate_artifact_sha256':sha(artifact),'command_sha256':sha(W/'command.json'),'input_hashes':inputs}
(W/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if result.returncode: raise SystemExit(result.returncode)
evidence=json.loads(out.read_text())
execution=evidence['execution']
report={'classification':'candidate-only full-OS-mask proof reuse against full-mask-candidate exact recorded artifact; one sample, not a distribution or worst-case bound',
    'source_mask_mode':'os','mask_layout':'full-mask','entropy_source':'OS getrandom via StateOnlyAttemptSecrets::generate (original run provenance)',
    'proof_reused':True,'fresh_mask_draw_in_this_run':False,'fixture_seed':20001,
    'proof_sha256':inputs['proof_sha256'],'public_sha256':inputs['public_sha256'],
    'candidate_artifact_sha256':inputs['candidate_elf_sha256'],'baseline_artifact_sha256':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34',
    'execution':{k:execution.get(k) for k in ['compute_units','error','declared_compute_unit_limit','serialized_transaction_bytes','return_data_sha256']},
    'submitted_fixture':evidence.get('fixture'),'gate_evidence_sha256':sha(out),
    'receipt':receipt}
(W/'full-mask-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'exit_status':0,'candidate_artifact':inputs['candidate_elf_sha256'],
    'proof':inputs['proof_sha256'],'full_mask':True,'compute_units':execution.get('compute_units'),
    'error':execution.get('error'),'tx_bytes':execution.get('serialized_transaction_bytes')}),flush=True)
