from pathlib import Path
import subprocess,json,hashlib,time,os
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');O=H/'dual-evidence/B-recommended';R=H/'dual-B-recommended';t=time.monotonic();cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
cmd=['python3',str(H/'recommended-extract.py'),'B-recommended']
r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'extract-time.log'),*cmd]);assert r.returncode==0
cmdmeta=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path','tools/r1-cost-probe/Cargo.toml','--offline','--locked','--format-version','1','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover']
with (O/'metadata-stderr.log').open('w') as se:meta=json.loads(subprocess.check_output(cmdmeta,cwd=R,stderr=se))
features=[{'name':next(p['name'] for p in meta['packages'] if p['id']==n['id']),'id':n['id'],'features':n['features']} for n in meta['resolve']['nodes']]
(O/'features.json').write_text(json.dumps(features,indent=2)+'\n')
pins=json.loads((H/'B-recommended-source.json').read_text());bad=[p for p,v in pins['files'].items() if hashlib.sha256((R/p).read_bytes()).hexdigest()!=v['sha256']];assert not bad,bad
symbols=(O/'symbols.txt').read_text().splitlines();fixtures=[s for s in symbols if any(k in s for k in ['fixture','test_hooks','forced_pole','generate_for_mask_nonce','ct_pole','no_pole','generate'])]
(O/'fixture-entropy-symbols.txt').write_text('\n'.join(fixtures)+'\n')
rec=dict(target=[cmd,cmdmeta,'source hash validation'],source_revision=pins['revision'],source_files=len(pins['files']),source_mismatches=bad,exit_status=0,wall_seconds=time.monotonic()-t,limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)')
(O/'static-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
