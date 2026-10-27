#!/usr/bin/env python3
"""Task-local host launch: read-only admission then one capped sequential scope."""
import pathlib,subprocess,shlex,json,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[2]
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-pv-dudect-20261027'
E=R/'evidence/pv-l3-20261027/dudect'; E.mkdir(parents=True,exist_ok=True)
def ssh(c,**kw):return subprocess.run(['ssh',H,c],text=True,capture_output=True,**kw)
if sys.argv[1]=='upload':
 p=ssh(f'mkdir -p {B}; python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py {B}/upload-admission.json > {B}/upload-reservation.log 2>&1; result=$?; cat {B}/upload-reservation.log; exit $result'); (E/'upload-reservation.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr);assert p.returncode==0
 roots=['Cargo.toml','Cargo.lock','.cargo','crates','programs','tools/r1-cost-probe','xtask','audit/poseidon-pair-probe','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/refine']
 files=subprocess.check_output(['git','ls-files',*roots],cwd=R,text=True).splitlines()
 files += [str(p.relative_to(R)) for p in (R/'tools/pv-dudect').rglob('*') if p.is_file() and 'target' not in p.parts and '__pycache__' not in p.parts]
 files=sorted(set(p for p in files if (R/p).is_file()))
 pins={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files};(E/'source-manifest.json').write_text(json.dumps(pins,indent=2)+'\n')
 assert ssh(f'mkdir -p {B}/src').returncode==0
 tar=subprocess.Popen(['tar','-cf','-','-T','-'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 tar.stdin.write(('\n'.join(files)+'\n').encode());tar.stdin.close()
 q=subprocess.run(['ssh',H,f'tar -xf - -C {B}/src'],stdin=tar.stdout);assert q.returncode==0;assert tar.wait()==0
 subprocess.run(['scp','-q',str(E/'source-manifest.json'),H+':'+B+'/'],check=True)
else:
 stage=sys.argv[1]
 cmd=f'cd {B} && python3 src/tools/pv-dudect/launch.py {shlex.quote(stage)}'
 p=ssh(cmd);(E/(stage+'-transport.log')).write_text(p.stdout+p.stderr);print(p.stdout+p.stderr);sys.exit(p.returncode)
