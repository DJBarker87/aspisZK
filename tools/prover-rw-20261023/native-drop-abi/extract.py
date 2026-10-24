"""One charged extraction/translation with independent cgroup admission."""
from pathlib import Path
import datetime,hashlib,json,os,re,runpy,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
D=Path(__file__).resolve().parent
E=H/'native-drop-abi'
a=int(sys.argv[1]);kind=sys.argv[2]
assert 36<=a<=44
O=E/f'extraction{a:03d}';O.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
candidate=15 if a==42 else 14
binary=E/f'backend/candidate-{candidate:03d}/main.exe'
receipt=E/f'backend/ProverRwNativeDropABI-build-{candidate:03d}/receipt.json'
assert sha(binary)==json.loads(receipt.read_text())['versioned_binary']['sha256']
if kind=='printer-charon':
 cmd=['python3',str(D/'printer-charon.py')]
 inputs=[D/'printer-charon.py',D/'printer-probe/lib.rs',D/'printer-probe/Cargo.toml',Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')]
elif kind in ['fixture-escape','fixture-capture']:
 cmd=['python3',str(D/'fixture-extract.py'),kind[8:]]
 inputs=[D/'fixture-extract.py',D/'fixtures/lib.rs',D/'fixtures/Cargo.toml',Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')]
elif kind=='nodrop-charon':
 charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--start-from','crate::increment','--dest-file',str(E/'ProverRwNativeDropNoDrop.llbc'),'--','--manifest-path',str(D.parent/'native-entropy/drop-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','4']
 inputs=[charon,D.parent/'native-entropy/drop-probe/lib.rs',D.parent/'native-entropy/drop-probe/Cargo.toml',D.parent/'native-entropy/drop-probe/Cargo.lock']
else:
 assert kind in ['nodrop','minimal','selected64','escape','escape-native','capture-native','printer']
 inp={'printer':E/'ProverRwNativeDropABIPrinter.llbc','nodrop':H/'native-drop/ProverRwNativeDropNoDrop.llbc','minimal':D.parent/'native-entropy/ProverRwNativeEntropyDropV5.llbc','selected64':D.parent/'rng-extractor/ProverRwRngExtractorselected64.llbc','escape-native':H/'native-drop/ProverRwNativeDropescape.llbc','capture-native':E/'ProverRwNativeDropcapture.llbc','escape':D.parent/'rng-extractor/ProverRwRngExtractornegative007.llbc'}[kind]
 cmd=[str(binary),'-sequential','-eval-drops','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','ProverRwNativeDropABI'+kind,'-dest',str(O/'raw-output'),'-split-files','-emit-json',str(inp)]
 inputs=[binary,receipt,inp]
if '-backend' in cmd:
 from drop_flags import assess
 base=E/f'backend/ProverRwNativeDropABI-build-{candidate:03d}'
 config=base/'Config.ml.txt'; main=base/'Main.ml.txt'
 flag_assessment=assess(cmd,config,main)
 built=json.loads(receipt.read_text())['candidate_source_sha256']
 assert built['src/Config.ml']==sha(config) and built['src/Main.ml']==sha(main)
 inputs += [config,main]
else:
 flag_assessment={'effective_drop_as_no_op':None,'assessment':'Charon source extraction only'}
scanner=runpy.run_path(str(D.parent/'native-entropy/reservation.py'))
before=scanner['admission']();(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(attempt=a,kind=kind,command=cmd,source_revision=f'78a5893610+candidate{candidate:03d}-unaccepted',source_sha256={str(p):sha(p) for p in [Path(__file__),*inputs]},print_axioms='N/A: extraction, not a Lean proof',accepted_artifact=False)
pre['drop_flags']=flag_assessment; pre['dependency_fingerprint']=sha(receipt);(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
assert before['allowed']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(H/'rng-charon-target'),PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
t=time.monotonic()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=H/'src',env=env,stdout=out,stderr=err)
metrics=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',metrics);return int(m[1]) if m else None
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=metrics)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n');print(json.dumps({k:pre[k] for k in ['attempt','kind','exit_status','wall_seconds','peak_rss_kib','swaps']}))
raise SystemExit(r.returncode)
