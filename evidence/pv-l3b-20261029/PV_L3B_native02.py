from pathlib import Path
import os,json,subprocess,hashlib,sys
D=Path(__file__).resolve().parent
old=D.parent/'codex-pv-rdea-20261028'
cfg=json.loads((old/'build-command.json').read_text())
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],**cfg['env'])
env['CARGO_TARGET_DIR']=str(D/'client-target')
env['CARGO_PROFILE_RELEASE_DEBUG']='2'
assert not env.get('RUSTFLAGS') and not env.get('CARGO_ENCODED_RUSTFLAGS')
record=dict(command=cfg['command'],env={k:env.get(k) for k in [*cfg['env'],'CARGO_PROFILE_RELEASE_DEBUG','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_PROFILE_RELEASE_STRIP']},phase='release compilation with full DWARF; no proof generation or arithmetic execution',only_codegen_change='debuginfo=2; strip remains default none',baseline=str(old/'client-deployed-baseline'))
(D/'debug-build-command.json').write_text(json.dumps(record,indent=2)+'\n')
sys.exit(subprocess.run(cfg['command'],env=env).returncode)
