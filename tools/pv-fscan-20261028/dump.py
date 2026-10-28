import pathlib,subprocess,json,os,sys,hashlib
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');S=D/'src';name,pkg,features,profile=sys.argv[1:5];tc=sys.argv[5] if len(sys.argv)>5 else '1.94.1';O=D/name;O.mkdir(exist_ok=True)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN=tc,RUSTC_BOOTSTRAP='1',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'target'),CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0')
cmd=['cargo','rustc','--manifest-path',str(S/'Cargo.toml'),'-p',pkg,'--lib','-j','4']
if profile=='release':cmd+=['--release']
if profile=='dev-unchecked':env.update(CARGO_PROFILE_DEV_DEBUG_ASSERTIONS='false',CARGO_PROFILE_DEV_OVERFLOW_CHECKS='false')
if features!='-':cmd+=['--features',features]
cmd+=['--','-Zmir-opt-level=0','--emit=mir'];(O/'command.json').write_text(json.dumps(dict(argv=cmd,env={k:v for k,v in env.items() if k.startswith(('CARGO','RUST'))}),indent=2))
r=subprocess.run(cmd,env=env);print('exit',r.returncode,flush=True)
if r.returncode:sys.exit(r.returncode)
a=list((D/'target'/('release' if profile=='release' else 'debug')/'deps').glob(pkg.replace('-','_')+'-*.mir'));a.sort(key=lambda p:p.stat().st_mtime,reverse=True);assert a
b=a[0].read_bytes();(O/'crate.mir').write_bytes(b);(O/'mir-identity.json').write_text(json.dumps(dict(path=str(a[0]),sha256=hashlib.sha256(b).hexdigest(),size=len(b)),indent=2));print('MIR',len(b),flush=True)
