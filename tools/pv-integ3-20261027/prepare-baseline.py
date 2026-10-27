from pathlib import Path
import subprocess,json,shlex
T=Path('tools/pv-integ3-20261027');D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298';H='dombarker@100.108.41.90';E=Path('evidence/pv-integ1-20261027/d298')
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
# Capture admission before copying any additional inputs.
cmd=f'python3 {G} {D}/baseline-upload-admission.json > {D}/baseline-upload-admission.log 2>&1'
r=subprocess.run(['ssh',H,cmd]);subprocess.run(['scp','-q',H+':'+D+'/baseline-upload-admission.json',str(E/'baseline-upload-admission.json')],check=True)
assert r.returncode==0 and json.loads((E/'baseline-upload-admission.json').read_text())['allowed'],r.returncode
subprocess.run(['ssh',H,'mkdir -p '+D+'/baseline/source'],check=True)
for name in ['native.py','reservation.py','capped-template.py']:
 data=(T/name).read_text().replace(D,D+'/baseline')
 subprocess.run(['ssh',H,'cat > '+D+'/baseline/'+name],input=data,text=True,check=True)
rev=subprocess.check_output(['git','rev-parse','37e5e133f8'],text=True)
subprocess.run(['ssh',H,'cat > '+D+'/baseline/source-revision.txt'],input=rev,text=True,check=True)
paths=['Cargo.toml','Cargo.lock','.cargo','crates','programs','audit','xtask','tools','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/z4']
p=subprocess.Popen(['git','archive','37e5e133f8',*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',H,'tar xf - -C '+D+'/baseline/source'],stdin=p.stdout);p.stdout.close();assert p.wait()==r.returncode==0
