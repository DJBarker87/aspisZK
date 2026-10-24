#!/usr/bin/env python3
"""One focused extraction/translation of the native-checked owned step."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');N=H/'s1-claims-row-step-v1-20261024';W=H/'s1-claims-row-owned-extract-v1-20261024';phase=sys.argv[1];assert phase in ['charon','aeneas']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 receipt=json.loads((N/'results/claims_row_write_preserves_initialized_prefix-v6/receipt.json').read_text());assert receipt['exit_status']==0
 W.mkdir(exist_ok=False)
 for name in ['frozen-probe','frozen-source']:shutil.copytree(N/name,W/name,ignore=shutil.ignore_patterns('target','.git'))
 for name in ['Cargo.toml','Cargo.lock']:shutil.copyfile(N/name,W/name)
 source=(N/'proofs.rs').read_text();body=source[source.index('fn owned_step('):source.index('\nfn row(')]
 p=W/'frozen-probe/src/r1_semantic.rs';s=p.read_text();s=s[:s.index('\n#[cfg(kani)]\n#[path="claims_write_proofs.rs"]')]
 decl='\ntype Claims = [[QM31;29];3];\ntype Row = [QM31;29];\n'+body.replace('fn owned_step(', 'pub fn claims_owned_step(')+'\n'
 p.write_text(s+decl)
 (W/'binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',native_source=str(N/'proofs.rs'),native_source_sha256=sha(N/'proofs.rs'),native_receipt_sha256=sha(N/'results/claims_row_write_preserves_initialized_prefix-v6/receipt.json'),owned_body=body,source_sha256=sha(p),qualification='Exact checked owned_step body, only public/name change, on the same complete native QM31/Error/array types. Not the allocation helper or the complete Claims loop.'),indent=2)+'\n')
else:assert W.exists() and not json.loads((W/'ClaimsOwned.llbc').read_text())['has_errors']
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip()[3:].lstrip('/');limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(1536*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0','pids.max':'64'},limits
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release');A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
if phase=='charon':cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--start-from','crate::r1_semantic::claims_owned_step','--include','crate::r1_semantic::claims_owned_step','--include','crate::r1_wire::Error','--dest-file',str(W/'ClaimsOwned.llbc'),'--','--manifest-path',str(W/'frozen-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']
else:cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1ClaimsOwnedStep','-dest',str(W/'generated'),'-subdir','AspisS1ClaimsOwnedStep','-split-files','-emit-json',str(W/'ClaimsOwned.llbc')]
out=W/phase;out.mkdir(exist_ok=False)
meta=dict(schema='focused-extractor-proof-packet-v1',command=cmd,limits=limits,binding=json.loads((W/'binding.json').read_text()),tools={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]},source_revision='640d3ebcf6',source_sha256=sha(W/'frozen-probe/src/r1_semantic.rs'),lock_sha256=sha(W/'Cargo.lock'),expected_time='Optimized focused owned row assignment source extraction, then translation; no arithmetic generation or package replay.')
(out/'input.json').write_text(json.dumps(meta,indent=2)+'\n');os.chdir(W);start=time.monotonic()
with (out/'stdout.log').open('w') as so,(out/'stderr.log').open('w') as se:status=subprocess.call(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],stdout=so,stderr=se)
tl=(out/'time.log').read_text()
def metric(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',tl);return int(m[1]) if m else None
r=dict(schema='focused-extractor-proof-packet-v1',command=cmd,exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),limits=limits,cgroup_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_current=int((cg/'memory.swap.current').read_text()),source_unchanged=sha(W/'frozen-probe/src/r1_semantic.rs')==meta['source_sha256'],lock_unchanged=sha(W/'Cargo.lock')==meta['lock_sha256'],input_sha256=sha(out/'input.json'),print_axioms='N/A: source extraction/translation, not a Lean theorem')
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));raise SystemExit(status)
