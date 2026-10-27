from NBB_host import *
import hashlib
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','tools/r1-builder-reference']
admit('NBB_SYNC001')
r=py(f'from pathlib import Path;p=Path({(B+"/NBB_src")!r});assert not p.exists();p.mkdir()')
assert r.returncode==0,r.stderr
# Stream tracked frozen source only. No artifact/cache corpus is duplicated.
archive=subprocess.Popen(['git','archive',rev,'--',*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',H,'tar -x -C '+shlex.quote(B+'/NBB_src')],stdin=archive.stdout,capture_output=True,text=True)
archive.stdout.close();assert archive.wait()==0 and r.returncode==0,r.stderr
(E/'NBB_ARCHIVE.json').write_text(json.dumps(dict(revision=rev,paths=paths,exit=r.returncode,stderr=r.stderr),indent=2)+'\n')
# Frozen lock is explicitly checked before any instrumentation.
r=ssh('sha256sum '+B+'/NBB_src/Cargo.lock');assert r.returncode==0
assert r.stdout.split()[0]=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(E/'NBB_FROZEN_LOCK.log').write_text(r.stdout)
