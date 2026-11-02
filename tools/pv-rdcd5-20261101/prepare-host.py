from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';D='/home/dombarker/project-offloads/codex-pv-rdcd5-20261101';H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
# Admission receipts precede every upload; scope runner repeats at launch.
r=subprocess.run(['ssh',H,f'mkdir -p {D}; python3 {G}/reservation.py {D}/upload-admission.json > {D}/upload-admission.log 2>&1'],capture_output=True,text=True)
for n in ['upload-admission.json','upload-admission.log']:
 q=subprocess.run(['ssh',H,f'cat {D}/{n}'],capture_output=True,text=True);assert q.returncode==0;qpath=E/n;qpath.write_text(q.stdout)
a=json.load(open(E/'upload-admission.json'));assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
records={}
for f in ['v233-h6-inputs.json','v237-h6-inputs.json']:records.update(json.load(open(R/'evidence/pv-rdcd4-20261029'/f))['records'])
(E/'h6-records.json').write_text(json.dumps(records,indent=2)+'\n')
manifest=subprocess.check_output(['git','show','research:evidence/pv-replay-20261027/receipts/external-object-manifest.json'],cwd=R)
(E/'external-object-manifest.json').write_bytes(manifest)
for p in [E/'source-resolution.json',E/'h6-records.json',E/'external-object-manifest.json',R/'tools/pv-rdcd5-20261101/preflight.py']:
 subprocess.run(['scp','-q',str(p),H+':'+D+'/'+p.name],check=True)
# Each source is the tracked authority, transported once after admission.
plan=json.load(open(E/'source-resolution.json'))
subprocess.run(['ssh',H,f'mkdir -p {D}/lean-sources/R1Z'],check=True)
for m,x in plan['modules'].items():
 subprocess.run(['scp','-q',str(R/x['path']),H+':'+D+'/lean-sources/'+m.replace('.','/')+'.lean'],check=True)
