#!/usr/bin/env python3
"""Exactly one selected native Kani attempt, independently capped; never retries."""
import hashlib,json,pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2];B=pathlib.Path(__file__).resolve().parent
E=R/'evidence/port22arena-20261024';H='/home/dombarker/project-offloads/port22arena-20261024';HOST='dombarker@100.108.41.90'
assert not (E/'kani-001.json').exists(), 'single Kani allowance already charged'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['rsync','-az',str(B)+'/',HOST+':'+H+'/'],check=True)
old=json.loads((R/'evidence/port20alloc-20261024/kani-002/receipt.json').read_text())
# All existing Kani tool/sysroot objects rehashed; historical source evidence is
# not relabelled as a new tool identity. No dependencies outside this crate.
code="""import hashlib,json,pathlib,sys
pins=json.load(sys.stdin)
for p,h in pins.items(): assert hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h,p
print(json.dumps(dict(verified_tool_sysroot_hashes=len(pins))))
"""
# Use a remote job-owned script rather than interpolating source into shell.
verify=B/'Port22ARENA_verify.py';verify.write_text(code)
subprocess.run(['scp','-q',str(verify),HOST+':'+H+'/'],check=True)
v=subprocess.check_output(['ssh',HOST,'python3',H+'/Port22ARENA_verify.py'],input=json.dumps(old['tool_sysroot_hashes']),text=True)
(E/'tool-preflight.json').write_text(v)
inputs={str(p.relative_to(B)):sha(p) for p in (B/'Port22ARENA-native').rglob('*') if p.is_file()}
inputs.update({f:sha(B/f) for f in ['Port22ARENA_gate.py','Port22ARENA_run.py','Port22ARENA_verify.py']})
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',H+'/Port22ARENA-native/Cargo.toml','--target-dir',H+'/Port22ARENA-kani-target','-j','1','-Z','unstable-options','--harness-timeout','120s','--exact','--harness','Port22ARENA_selected_alloc_frame','--output-format','terse']
env=old['env'];env['CARGO_TARGET_DIR']=H+'/Port22ARENA-target'
cfg=dict(attempt='kani-001',kind='kani',command=cmd,input_hashes=inputs,tool_sysroot_hashes=old['tool_sysroot_hashes'],rustc=old['rustc'],sysroot=old['sysroot'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),selected_source_sha256=sha(E/'selected-source.json'),expected_time='optimized compilation then SAT for selected BumpAllocator cursor-store frame; no arithmetic elimination',env=env)
p=E/'kani-001.json';p.write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(p),HOST+':'+H+'/'],check=True)
for label in ['preflight','go']:
 with (E/('kani-001-'+label+'.json')).open('w') as f:
  r=subprocess.run(['ssh',HOST,'python3',H+'/Port22ARENA_gate.py'],stdout=f)
 if r.returncode:sys.exit(r.returncode)
r=subprocess.run(['ssh',HOST,'systemd-run','--user','--scope','-q','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',H+'/Port22ARENA_run.py','kani-001.json'])
subprocess.run(['scp','-qr',HOST+':'+H+'/kani-001',str(E/'kani-001')],check=True)
sys.exit(r.returncode)
