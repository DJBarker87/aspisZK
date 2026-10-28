import pathlib,os,subprocess,sys,json,hashlib
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');name,tc,checks=sys.argv[1:];O=D/name;O.mkdir(exist_ok=True)
cmd=['/home/dombarker/.cargo/bin/rustup','run',tc,'rustc','--edition=2021','--crate-type=lib','-Copt-level=3','-Cdebug-assertions='+checks,'-Coverflow-checks='+checks,'-Zmir-opt-level=4','--emit=mir','-o',str(O/'crate.mir'),str(D/'std-probe.rs')]
env=dict(os.environ,RUSTC_BOOTSTRAP='1');r=subprocess.run(cmd,env=env);(O/'command.json').write_text(json.dumps(dict(argv=cmd,toolchain=tc,checks=checks),indent=2));
if not r.returncode:
 b=(O/'crate.mir').read_bytes();(O/'mir-identity.json').write_text(json.dumps(dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())));print('MIR bytes',len(b))
sys.exit(r.returncode)
