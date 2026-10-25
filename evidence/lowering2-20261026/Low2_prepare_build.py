#!/usr/bin/env python3
"""Prepare private reproducible source/cache inputs; never edits shared inputs."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]; E=Path(__file__).resolve().parent
H='/home/dombarker/project-offloads/codex-cx-lowering2-20261026'
old='/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023'
remote='dombarker@100.108.41.90'
paths=['Cargo.toml','Cargo.lock','.cargo','crates','programs','audit','xtask','docs/research/v8-r0-zk-20261009/refine','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3']
files=subprocess.check_output(['git','ls-files','-z','--',*paths],cwd=R).split(b'\0')
files=[p.decode() for p in files if p]
manifest={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'files':{p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files}}
(E/'Low2_build_inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['ssh',remote,'mkdir -p '+H+'/src'],check=True)
# Stream only tracked source. No local archive or binary retained.
a=subprocess.Popen(['tar','-cf','-','--null','-T','-'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
b=subprocess.Popen(['ssh',remote,'tar -xf - -C '+H+'/src'],stdin=a.stdout)
a.stdout.close();a.communicate(('\0'.join(files)+'\0').encode());assert a.returncode==0;assert b.wait()==0
s=(R/'tools/s10-repin3-20261023/build-host.py').read_text().replace(old,H)
s=s.replace("'devnet':None", "'devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'")
s=s.replace("assert mode == 'devnet' or result['byte_identical'],result", "assert result['byte_identical'],result")
# Use an unchanged compiled cache as seed, forcing recompilation of source.
s=s.replace("H.parent/'codex-cx-s10-inventory3-20261021'/target.name", "H.parent/'codex-cx-s10-repin3-20261023'/target.name")
(E/'Low2_build_host.py').write_text(s)
subprocess.run(['scp','-q',str(E/'Low2_build_host.py'),remote+':'+H+'/build-host.py'],check=True)
subprocess.run(['scp','-q',str(R/'tools/s10-repin3-20261023/rustc-diagnostics.py'),remote+':'+H+'/rustc-diagnostics.py'],check=True)
subprocess.run(['ssh',remote,'chmod +x '+H+'/rustc-diagnostics.py'],check=True)
subprocess.run(['scp','-q',str(E/'Low2_build_inputs.json'),remote+':'+H+'/source-inputs.json'],check=True)
