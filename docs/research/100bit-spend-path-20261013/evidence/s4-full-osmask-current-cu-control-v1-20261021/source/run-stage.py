from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time
W=Path(__file__).resolve().parent
C=json.loads((W/'config.json').read_text())
PHASE=sys.argv[1]
assert PHASE in C['phases']
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={k:(CG/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
want=C['phases'][PHASE]
assert limits=={'memory.high':str(want['memory_high_bytes']),'memory.max':str(want['memory_max_bytes']),'memory.swap.max':'0'},limits
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
DRIVER=W/'driver';BIN=Path(C['target_dir'])/'release/pool_gate_osmask'
PROOF=W/'input/proof.bin';PUBLIC=W/'input/public.bin'
assert sha(DRIVER/'src/bin/pool_gate.rs')==C['pool_gate_source_sha256']
assert sha(PROOF)==C['proof_sha256'] and sha(PUBLIC)==C['public_sha256']

def run(cmd,cwd,env,folder,timeout):
    folder.mkdir(parents=True,exist_ok=False)
    (folder/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
    before=(CG/'memory.events').read_text();start=time.monotonic()
    with (folder/'output.log').open('w') as log:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(folder/'time.log'),*cmd],cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    timing=(folder/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
    rec={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_peak_bytes':int((CG/'memory.peak').read_text()),'swap_current_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text(),'limits':limits,'command':cmd}
    (folder/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    return rec

env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true')
if PHASE=='build':
    env['CARGO_TARGET_DIR']=C['target_dir']
    cmd=['/home/dombarker/.cargo/bin/cargo','build','--release','--manifest-path',str(DRIVER/'Cargo.toml'),'--bin','pool_gate_osmask','--features','private-leaf-salts','--locked','--offline','-j','1']
    rec=run(cmd,DRIVER,env,W/'build-evidence',300)
    assert BIN.is_file(),str(BIN)
    rec.update({'binary':str(BIN),'binary_sha256':sha(BIN),'binary_bytes':BIN.stat().st_size,'source_sha256':sha(DRIVER/'src/bin/pool_gate.rs'),'manifest_sha256':sha(DRIVER/'Cargo.toml'),'lock_sha256':sha(DRIVER/'Cargo.lock')})
    (W/'build-evidence/receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    help_result=subprocess.run([str(BIN),'--help'],capture_output=True,text=True)
    (W/'build-evidence/help.txt').write_text(help_result.stdout+help_result.stderr)
    assert '--seed' in help_result.stdout+help_result.stderr and '--uniform-lane' in help_result.stdout+help_result.stderr
    print(json.dumps(rec),flush=True)
else:
    assert BIN.is_file() and sha(BIN)==json.loads((W/'build-evidence/receipt.json').read_text())['binary_sha256']
    rows=[]
    for label,elf,expected in [('frozen-default',Path(C['baseline_elf']),C['baseline_elf_sha256']),('combined-candidate',Path(C['candidate_elf']),C['candidate_elf_sha256'])]:
        assert sha(elf)==expected
        task=W/'tasks'/label;task.mkdir(parents=True,exist_ok=False)
        proof=task/'proof.bin';public=task/'public.bin';shutil.copyfile(PROOF,proof);shutil.copyfile(PUBLIC,public)
        evidence=task/'evidence.json';out=task/'task'
        cmd=[str(BIN),C['pool_elf'],str(elf),C['registry_elf'],str(evidence),str(out),'transfer','success','--pairs','0','--seed','20001','--split','10','--uniform-lane','--tx-version','v1','--zeroed-genesis-page','--reuse',str(proof),str(public)]
        rec=run(cmd,W,env,W/'run-evidence'/label,180)
        result={'label':label,'elf_sha256':sha(elf),'proof_sha256':sha(proof),'public_sha256':sha(public),'proof_bytes':proof.stat().st_size,'source_mask_mode':'os','mask_layout':'full-mask','runner_receipt':rec}
        if evidence.is_file():
            ev=json.loads(evidence.read_text());result['gate_evidence']=ev;result['evidence_sha256']=sha(evidence)
        (W/'run-evidence'/label/'result.json').write_text(json.dumps(result,indent=2)+'\n');rows.append(result)
    comparison={'classification':'one retained full-mask proof produced with OS entropy; original pinned driver regenerates matching public statement then reuses the exact same proof/public against frozen default and combined candidate ELFs; not a distribution or worst-case CU bound','proof_sha256':C['proof_sha256'],'public_sha256':C['public_sha256'],'proof_bytes':57607,'baseline_elf_sha256':C['baseline_elf_sha256'],'candidate_elf_sha256':C['candidate_elf_sha256'],'pool_gate_source_sha256':C['pool_gate_source_sha256'],'pool_elf_sha256':C['pool_elf_sha256'],'registry_elf_sha256':C['registry_elf_sha256'],'runs':rows}
    (W/'comparison.json').write_text(json.dumps(comparison,indent=2)+'\n');print(json.dumps(comparison),flush=True)
