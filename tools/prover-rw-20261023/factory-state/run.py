"""Single-use capped selected extraction; denial still writes a full receipt."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,sys,time,traceback
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=int(sys.argv[1]);assert a in [54,55]
O=D/'packet'/f'extraction{a:03d}';O.mkdir(parents=True)
start=time.monotonic()
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
B=D.parent/'native-drop-abi/backend'
binary=B/'candidate-014/main.exe';br=B/'ProverRwNativeDropABI-build-014/receipt.json'
llbc=D/'ProverRwFactoryState.llbc'
if a==54:
    cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--include','zeroize','--start-from','crate::ProverRwFactoryStateDraw::resume','--dest-file',str(llbc),'--','--manifest-path',str(D/'preflight/Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','4']
    phase='optimized selected resume compilation and precise built-MIR extraction; actual Drop retained'
else:
    assert (D/'packet/extraction054/receipt.json').is_file()
    previous=json.loads((D/'packet/extraction054/receipt.json').read_text())
    assert previous['exit_status']==0 and previous['actual_target_invocations']==1
    assert previous['outputs'][0]['sha256']==sha(llbc)
    cmd=[str(binary),'-sequential','-eval-drops','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','ProverRwFactoryState','-dest',str(O/'raw-output'),'-split-files','-emit-json',str(llbc)]
    phase='selected deterministic resume translation; unaccepted existing candidate014; no backend build'
pre=dict(schema='ProverRwFactoryState-extraction-v1',attempt=a,command=cmd,
    source_revision=(D/'revision.txt').read_text().strip(),expected_phase=phase,
    actual_target_invocations=0,scope_invocations=0,charged_extraction_slots=1,
    accepted_artifact=False,print_axioms='N/A: extraction only; no Lean theorem')
code=1
try:
    assert sha(binary)==json.loads(br.read_text())['versioned_binary']['sha256']
    def source_input(p):
        return p.is_file() and not any(x in ['packet','target','__pycache__','runner-logs'] or x.startswith('diagnostics') for x in p.relative_to(D).parts)
    inputs=[p for p in D.rglob('*') if source_input(p)]
    originals=[D.parent/'factory-iteration/production-source.txt',D.parent/'factory-iteration/proof-cut/selected.rs',D.parent/'factory-iteration/RELATION.md',D.parent/'factory-source/RELATION.md']
    inputs += originals
    registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
    for name in ['zeroize-1.8.1','getrandom-0.3.4','libc-0.2.186','cfg-if-1.0.4']:
        p=registry/name;assert p.is_dir();inputs += [q for q in p.rglob('*') if q.is_file()]
    tc=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
    assert tc.is_dir()
    # Includes ALL sysroot rlibs, shared libraries, compiler/tools and metadata.
    inputs += [p for sub in ['bin','lib','etc'] for p in (tc/sub).rglob('*') if p.is_file()]
    inputs += [p for p in tc.iterdir() if p.is_file()]
    inputs += [charon,binary,br,B/'ProverRwNativeDropABI-build-014/Config.ml.txt',B/'ProverRwNativeDropABI-build-014/Main.ml.txt',Path('/usr/bin/time'),Path('/home/dombarker/.cargo/bin/rustup')]
    pins={str(p):sha(p) for p in sorted(set(inputs))}
    pre.update(source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),sysroot_rlib_count=sum(p.suffix=='.rlib' and p.is_relative_to(tc) for p in set(inputs)))
    assert pre['sysroot_rlib_count']>0
    if a==55:
        pre['drop_flags']=runpy.run_path(str(D/'drop_flags.py'))['assess'](cmd,B/'ProverRwNativeDropABI-build-014/Config.ml.txt',B/'ProverRwNativeDropABI-build-014/Main.ml.txt')
    (O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
    # Preserve originals before any compiler reservation.
    for p in D.rglob('*'):
        if source_input(p):
            dest=O/'source-inputs'/p.relative_to(D);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
    for p in originals:
        dest=O/'original-inputs'/p.relative_to(D.parent);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
    before=runpy.run_path(str(D/'reservation.py'))['admission'](requested=2*2**30)
    (O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
    assert before['allowed'],'fresh before admission denied; no scope/compiler launched'
    env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'target'))
    scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
    pre.update(scope_command=scope,scope_invocations=1)
    with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:
        code=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err).returncode
    pre['actual_target_invocations']=int((O/'target-started.json').exists())
except Exception:
    with (O/'stderr.log').open('a') as err:traceback.print_exc(file=err)
finally:
    s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
    def metric(n):
        m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
    pre.update(exit_status=code,wall_seconds=time.monotonic()-start,
        peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),
        target_timing='measured in time.log' if s else 'N/A: target not launched; outer runner timed separately',
        outputs=[dict(path=str(p),sha256=sha(p),size=p.stat().st_size) for p in ([llbc] if a==54 else list((O/'raw-output').rglob('*'))) if p.is_file()],
        postrun_changed_inputs=[p for p,h in pre.get('source_sha256',{}).items() if sha(p)!=h])
    (O/'stdout.log').touch(exist_ok=True)
    (O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','actual_target_invocations','scope_invocations']}))
raise SystemExit(code)
