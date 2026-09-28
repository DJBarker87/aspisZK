#!/usr/bin/env python3
"""Focused cached Lean leaf only; no dependency build or manifest replay."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--revision',default='a0f2d200c295f3028a12e1142a39a026d19bf1a0');a=p.parse_args();assert not a.output.exists();a.output.mkdir()
workspace=Path('/home/dombarker/project-offloads/aeneas-patched11-inspect/backends/lean')
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1')
cmd=['/usr/bin/time','-v','/home/dombarker/.elan/bin/lake','env','lean',str(a.source)]
with (a.output/'compile.log').open('w')as f:r=subprocess.run(cmd,cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
metadata={'target':str(a.source),'source_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'source_base_revision':a.revision,'workspace':str(workspace),'command':cmd,'exit':r.returncode,'toolchain':(workspace/'lean-toolchain').read_text().strip(),'scope':'symbolic arithmetic leaf; not Rust refinement or privacy'}
(a.output/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n');print((a.output/'compile.log').read_text());raise SystemExit(r.returncode)
