#!/usr/bin/env python3
"""D299 off-window upload/launch; no marker writes or window exemptions."""
import pathlib,subprocess,json,hashlib,sys,shlex
R=pathlib.Path(__file__).resolve().parents[2]
B='/home/dombarker/project-offloads/codex-pv-dudect-20261027'
H='dombarker@100.108.41.90';E=R/'evidence/pv-l3-20261027/dudect/d299';E.mkdir(exist_ok=True)
def ssh(cmd):return subprocess.run(['ssh',H,cmd],text=True,capture_output=True)
stage=sys.argv[1]
if stage=='upload':
 cmd=f'test ! -e /home/dombarker/project-offloads/QUIET_WINDOW.json && python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py {B}/d299-upload-admission.json > {B}/d299-upload-reservation.log 2>&1'
 p=ssh(cmd);subprocess.run(['scp','-q',H+':'+B+'/d299-upload-reservation.log',str(E)],check=True)
 subprocess.run(['scp','-q',H+':'+B+'/d299-upload-admission.json',str(E)],check=True)
 assert p.returncode==0 and json.loads((E/'d299-upload-admission.json').read_text())['allowed'] is True
 roots=['Cargo.toml','Cargo.lock','.cargo','crates','programs','tools/r1-cost-probe','xtask','audit/poseidon-pair-probe','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/refine']
 files=subprocess.check_output(['git','ls-files',*roots],cwd=R,text=True).splitlines()
 files += [str(p.relative_to(R)) for p in (R/'tools/pv-dudect').rglob('*') if p.is_file() and 'target' not in p.parts and '__pycache__' not in p.parts]
 files=sorted(set(p for p in files if (R/p).is_file()))
 (E/'source-manifest.json').write_text(json.dumps({p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files},indent=2)+'\n')
 tar=subprocess.Popen(['tar','-cf','-','-T','-'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 tar.stdin.write(('\n'.join(files)+'\n').encode());tar.stdin.close()
 q=subprocess.run(['ssh',H,f'tar -xf - -C {B}/src'],stdin=tar.stdout);assert q.returncode==0 and tar.wait()==0
 subprocess.run(['scp','-q',str(E/'source-manifest.json'),H+':'+B+'/source-manifest.json'],check=True)
else:
 assert stage in ['build-harness','build-candidate','compare','dry']
 p=ssh(f'test ! -e /home/dombarker/project-offloads/QUIET_WINDOW.json && cd {B} && python3 src/tools/pv-dudect/launch.py {shlex.quote(stage+"@d299")}')
 (E/(stage+'-transport.log')).write_text(p.stdout+p.stderr);print(p.stdout+p.stderr)
 for name in [stage+'@d299',stage+'@d299-admission.json',stage+'@d299-reservation.log']:
  subprocess.run(['scp','-qr',H+':'+B+'/'+name,str(E)],check=True)
 sys.exit(p.returncode)
