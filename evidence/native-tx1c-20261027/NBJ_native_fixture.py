from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBJ_host as h
h.admit('NBJ_NATIVEUPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBJ_copy_native.rs")!r}).write_text({(E/"NBJ_copy_native.rs.txt").read_text()!r})');assert r.returncode==0,r.stderr
code="import subprocess;from pathlib import Path;subprocess.run(['/home/dombarker/.cargo/bin/rustc','+1.94.1','--version','--verbose'],check=True);subprocess.run(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-C','opt-level=3','-C','overflow-checks=on','NBJ_copy_native.rs','-o','NBJ_copy_native.bin'],check=True);subprocess.run(['./NBJ_copy_native.bin'],check=True)"
cfg=dict(attempt='NBJ_R001',kind='rust',sources=['NBJ_copy_native.rs'],command=['python3','-c',code],timeout=120,env={'CARGO_NET_OFFLINE':'true'},deps_fingerprint={'dependencies':'Rust std only, no Cargo resolution; pinned rustc1.94.1','input':'K050 concrete playback values'},expected_time='optimized compilation of one tiny Rust fixture, then exact selected-copy execution')
(E/'NBJ_R001.json').write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBJ_host.py'),'NBJ_R001']);sys.exit(r.returncode)
