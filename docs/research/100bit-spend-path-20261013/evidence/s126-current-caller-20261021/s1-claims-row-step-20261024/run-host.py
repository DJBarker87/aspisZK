#!/usr/bin/env python3
"""One scoped normal-return control gate; retains errors and all source pins."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time
W = Path(__file__).resolve().parent
target = sys.argv[1]
attempt = sys.argv[2] if len(sys.argv) > 2 else 'v1'
H = Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
out = W/'results'/(target+'-'+attempt)
out.mkdir(parents=True,exist_ok=False)
cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip()[3:].lstrip('/')
limits = {n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits == {'memory.high':str(1536*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0','pids.max':'64'}, limits
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(2**20),b''):h.update(chunk)
    return h.hexdigest()
def native_imports():
    K=Path('/home/dombarker/.kani/kani-0.67.0')
    files=[K/'rustc-version',K/'rust-toolchain-version',K/'toolchain/bin/rustc']
    for root in [K/'lib',K/'toolchain/lib',K/'library',K/'no_core']:
        for p in root.rglob('*'):
            if p.is_file() and (p.suffix in ['.rlib','.rmeta','.so','.rs','.toml']):files.append(p)
    return {str(p):sha(p) for p in files}

def sources(root):
    result = {}
    for directory,dirs,files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in ['.git','target','.lake','results']]
        for name in files:
            p = Path(directory)/name
            if p.suffix in ['.rs','.toml','.lock','.py']: result[str(p.relative_to(root))] = sha(p)
    return result
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', CARGO_BUILD_JOBS='1',
    CARGO_NET_OFFLINE='true', CARGO_TARGET_DIR=str(H/'target'),
    RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
os.chdir(W)
metadata_cmd = ['cargo','metadata','--manifest-path',str(W/'Cargo.toml'),'--offline','--format-version','1']
metadata = subprocess.run(metadata_cmd,text=True,capture_output=True,env={**os.environ,'RUSTFLAGS':''})
(out/'metadata-stderr.log').write_text(metadata.stderr)
assert metadata.returncode == 0, metadata.stderr
m = json.loads(metadata.stdout)
dependencies = {p['manifest_path']:sources(Path(p['manifest_path']).parent) for p in m['packages'] if p['source'] is None}
tools = {str(p):sha(p) for p in Path('/home/dombarker/.kani/kani-0.67.0/bin').iterdir() if p.is_file()}
cmd = ['cargo','kani','--manifest-path',str(W/'Cargo.toml'),'--lib','--exact','--harness','r1_semantic::claims_write_proofs::'+target,
       '--solver','cadical','--no-assertion-reach-checks','-j','1','-Z','unstable-options',
       '-Z','stubbing','--output-format','terse','--harness-timeout','180',
       '--cbmc-args','--unwinding-assertions']
native_before=native_imports()
workspace_before={name:sha(W/name) for name in ['Cargo.toml','Cargo.lock','source-binding.json','proofs.rs','run-host.py','admit-host.py','HostAdmission.py','prepare-host.py']}
input_record = dict(workspace_pins=workspace_before,native_imports=native_before, rustc_version=(Path('/home/dombarker/.kani/kani-0.67.0/rustc-version')).read_text().strip(),schema='focused-extractor-proof-packet-v1',command=cmd,
    metadata_command=metadata_cmd, source_pins=dependencies, tools=tools,limits=limits,
    expected_time='Cached optimized source compilation, then one partial-initialization pointer write step with the real decoder callee abstracted at its normal-return boundary; no field arithmetic solving.',
    environment={k:os.environ[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},
    qualification='One exact shipped claims-loop iteration on the real Box/MaybeUninit/full-QM31 carrier; private ValidatedRecord and WireError retained. Verified decode_k normal-return boundary is abstracted with complete argument checks and arbitrary full row or error. Loop-domain p in 0..3 and initialized-prefix invariant are explicit. Allocation is harness setup, not uninit allocator/cleanup or whole claims/SDK/SBF correspondence.')
(out/'input.json').write_text(json.dumps(input_record,indent=2)+'\n')
before = (cg/'memory.events').read_text()
start = time.monotonic()
with (out/'stdout.log').open('w') as so, (out/'stderr.log').open('w') as se:
    status = subprocess.call(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],stdout=so,stderr=se)
wall = time.monotonic()-start
unchanged = {p:sources(Path(p).parent)==pins for p,pins in dependencies.items()}
tl = (out/'time.log').read_text()
def metric(label):
    match = re.search(re.escape(label)+r':\s*(\d+)',tl)
    return int(match[1]) if match else None
receipt = dict(schema='focused-extractor-proof-packet-v1',command=cmd,exit_status=status,
    wall_seconds=wall,peak_rss_kib=metric('Maximum resident set size (kbytes)'),
    swaps=metric('Swaps'),cgroup_peak_bytes=int((cg/'memory.peak').read_text()),
    cgroup_swap_current=int((cg/'memory.swap.current').read_text()),limits=limits,
    memory_events_before=before,memory_events_after=(cg/'memory.events').read_text(),
    sources_unchanged=unchanged,print_axioms='N/A: Kani control certificate, not Lean',
    workspace_unchanged={name:sha(W/name)==h for name,h in workspace_before.items()},native_imports_unchanged=(native_imports()==native_before),input_sha256=sha(out/'input.json'))
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert all(unchanged.values()) and all(receipt['workspace_unchanged'].values()) and receipt['native_imports_unchanged'], unchanged
print(json.dumps(receipt))
raise SystemExit(status)
