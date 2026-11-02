"""Regenerate previously uncommitted NEF inputs without writing its directory."""
from pathlib import Path
import subprocess,json,hashlib,re,sys,time
E=Path(__file__).resolve().parent;R=E.parent.parent;F=R/'evidence/slice-q-fnptr-20261029'
W=Path('/private/tmp/NEO_specialisation_review_20261102');D=W/'evidence/slice-q-fnptr-20261029';D.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
 if p.name=='evidence':continue
 q=W/p.name
 if not q.exists():q.symlink_to(p)
for p in (R/'evidence').iterdir():
 q=W/'evidence'/p.name
 if not q.exists():q.symlink_to(p)
names=['NEF_FNPTR_SPECIALISATION.py','NEF_OBSERVER_CERTIFICATE.py','NEF_SPECIALISATION_TESTS.py','NEF_SOURCE_PINS.json']
for name in names:(D/name).write_bytes((F/name).read_bytes())
lines=(F/'NEF_REFERENCE_INPUTS.patch').read_text().splitlines(True);i=0;restored={}
while i<len(lines):
 assert lines[i]=='--- /dev/null\n';i+=1
 assert lines[i].startswith('+++ b/');name=lines[i][6:].strip();i+=1
 assert re.fullmatch(r'NEF_[A-Za-z0-9_]+\.rs\.txt',name)
 m=re.fullmatch(r'@@ -0,0 \+1,(\d+) @@\n',lines[i]);assert m;i+=1
 buf=[]
 for _ in range(int(m[1])):assert lines[i].startswith('+');buf.append(lines[i][1:]);i+=1
 restored[name]=''.join(buf);(D/name).write_text(restored[name])
start=time.monotonic();records=[]
for script in ['NEF_FNPTR_SPECIALISATION.py','NEF_SPECIALISATION_TESTS.py']:
 r=subprocess.run([sys.executable,str(D/script)],cwd=W,text=True,capture_output=True)
 records.append(dict(script=script,exit=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0,r.stdout+r.stderr
for name in ['NEF_SPECIALISATION_PAYLOAD.json','NEF_SPECIALISATION.patch','NEF_FNPTR_SPECIALISATION.json']:
 restored[name]=(D/name).read_text()
assert restored['NEF_SPECIALISATION.patch']==(F/'NEF_SPECIALISATION.patch').read_text(),'regenerated specialization differs'
(E/'NEO_SPECIALISATION_INPUTS.json').write_text(json.dumps(restored,indent=1)+'\n')
(E/'NEO_SPECIALISATION_TEST_RESULTS.json').write_bytes((D/'NEF_SPECIALISATION_TEST_RESULTS.json').read_bytes())
(E/'NEO_SPECIALISATION_RECEIPT.json').write_text(json.dumps(dict(exit_status=0,wall_seconds=time.monotonic()-start,records=records,input_sha256={n:hashlib.sha256(s.encode()).hexdigest() for n,s in restored.items()},script_sha256={n:hashlib.sha256((F/n).read_bytes()).hexdigest() for n in names},frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',status='PASS; requested evidence for lead adoption consideration, CM31 inverse remains OPEN until adoption and complete bridge',prover_runs=0,print_axioms='N/A: unchanged source-certificate tests'),indent=1)+'\n')
print(json.dumps(dict(restored_inputs=len(restored),tests=records[-1]['stdout'])))
