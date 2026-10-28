from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
label=sys.argv[1];files=sys.argv[2:];assert label.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'python3 {G}/reservation.py {D}/upload-{label}.json > {D}/upload-{label}.log 2>&1'],capture_output=True,text=True)
q=subprocess.run(['ssh',H,f'cat {D}/upload-{label}.json'],capture_output=True,text=True);(E/f'upload-{label}.json').write_text(q.stdout)
assert r.returncode==0 and json.loads(q.stdout).get('allowed') is True,'admission refused: wait 3 minutes then retry'
for f in files:
 p=R/f;assert p.is_file();subprocess.run(['scp','-q',str(p),H+':'+D+'/'+p.name],check=True)
