from NIV_formal import *
files={n:(E/n).read_text() for n in ['NIV_stage.py','NIV_warm_host.py','NIV_OPACITY.json']}
env={'CARGO_TARGET_DIR':B+'/NIV_NHR_target','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'4','RUSTUP_TOOLCHAIN':'nightly-2026-09-17','RUSTFLAGS':'-Zthreads=1 -C link-arg=-Wl,--threads=1','RAYON_NUM_THREADS':'1'}
r=run('NIV_L017','rust','frozen_deployed_dependency_warm',['python3','NIV_warm_host.py'],files,env);assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=['NIV_NHR_RESET_FIRST.json','NIV_NHR_RESET.json','NIV_WARM_LAUNCHED.json','NIV_WARM_RESULT.json']
names+=['NIV_warm/NHR_GRAPH_CHECK.json']
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print('PASS_AUTHORIZED_SINGLE_WARM_BUILD',flush=True)
