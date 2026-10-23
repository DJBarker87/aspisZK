"""Extract one actual result child; no copied implementation or child-success stub."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023';T=Path(__file__).parent
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2k-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
phase=sys.argv[1];n=int(sys.argv[2]);a=f'extract-{n:03d}';assert phase in ['charon','aeneas'];assert not (E/a).exists()
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
name='S2K_ResultValidationSource'
# The result crate's dev-dependency resolution requires the FULL frozen lock;
# the Kani harness lock intentionally excludes those dev dependencies.
subprocess.run(['scp',str(R/'Cargo.lock'),HOST+':'+H+'/S2K-root-Cargo.lock'],check=True)
lock=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\nb=Path('+repr(H)+')\np=b/"S2K-root-Cargo.lock";q=b/"native-source/Cargo.lock"\nif q.exists() and q.read_bytes()!=p.read_bytes(): (b/"c3-pre-root-Cargo.lock.txt").write_bytes(q.read_bytes())\nq.write_bytes(p.read_bytes())\nprint(json.dumps(dict(sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size,origin="worktree Cargo.lock")))\n').encode()))

cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::pool_v1::pair_forest_terminal::validate_result','--dest-file',H+'/'+name+'.llbc','--','--manifest-path',H+'/native-source/crates/aspis-statement/Cargo.toml','--offline','--release','--lib','--jobs','1'] if phase=='charon' else [aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',name,'-dest',H+'/c3-generated','-subdir',name,'-split-files','-emit-json',H+'/'+name+'.llbc']
if phase=='aeneas' and len(sys.argv)>3: cmd[1:1]=['-log','Translate']
if phase=='charon' and len(sys.argv)>3:
 cmd[2:2]=['--opaque','crate::pool_v1::pair_terminal::encode_pool_v1_pair_verified_afterstate_v1','--opaque','crate::atomic_statement::encode_digest_canonical','--opaque','crate::pool_v1::pair_forest_accounts::pool_v1_pair_forest_output_lane_v1','--include','core::option::Option']
 deps_note='afterstate encoder body reused from the exact existing extracted source and S2K_AfterstateEncoding; no successful-child stub'
pins=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\npaths='+repr([charon,charon+'-driver',aeneas])+'\nprint(json.dumps({p:dict(sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),bytes=Path(p).stat().st_size) for p in paths}))\n').encode()))
deps=dict(native_source_manifest_sha256=sha(E/'native-source.json'),cargo_lock=lock,tools=pins,scope='actual native private validate_result and its reachable dependencies; no whole-function Kani harness',reuse_policy='opaque pure children MUST resolve to exact existing extracted definitions; no opaque/axiom declarations may be installed in Lean')
if phase=='aeneas':
 deps['llbc']=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\np=Path('+repr(H+'/'+name+'.llbc')+')\nx=json.loads(p.read_text());assert not x["has_errors"]\nprint(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,has_errors=x["has_errors"])))\n').encode()))
x=dict(attempt=a,kind=phase,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,sources=['native-source/'+f for f in json.loads((E/'native-source.json').read_text())],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=H+'/c3-charon-target',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4'),deps_fingerprint=deps,expected_time='optimized compilation/MIR extraction or one result-validation translation; no arithmetic elimination or manifest replay')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
subprocess.run(['scp',str(E/(a+'.json')),str(T/'S2K_run_host.py'),HOST+':'+H+'/'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2K_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2K_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True)
subprocess.run(['scp',HOST+':'+H+'/native-source/Cargo.lock',str(E/a/'resolved-Cargo.lock.txt')],check=True)
if phase=='aeneas' and r.returncode==0:subprocess.run(['scp','-r',HOST+':'+H+'/c3-generated',str(E/(a+'-generated'))],check=True)
sys.exit(r.returncode)
