from pathlib import Path
import json,lzma,subprocess,hashlib,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,time,hashlib
p=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');s=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py');b=s.read_bytes()
print(json.dumps({'epoch':time.time(),'marker':json.loads(p.read_text())if p.exists()else None,'mtime_epoch':p.stat().st_mtime if p.exists()else None,'ctime_epoch':p.stat().st_ctime if p.exists()else None,'scanner_source':b.decode(),'scanner_sha256':hashlib.sha256(b).hexdigest()}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;d=json.loads(r.stdout);source=d.pop('scanner_source');(E/'shared-reservation.readonly.py').write_text(source)
# Retain the first committed lock/marker observation, rather than inventing launch-time snapshots.
rev=subprocess.check_output(['git','log','--reverse','--format=%H','--','evidence/pv-k3scan-20261101/D549-LOCKS.json.xz'],text=True).splitlines()[0];checkpoint=json.loads(lzma.decompress(subprocess.check_output(['git','show',rev+':'+'evidence/pv-k3scan-20261101/D549-LOCKS.json.xz'])));d['early_checkpoint']={'revision':rev,'epoch':checkpoint['epoch'],'quiet_window':checkpoint['quiet_window']};launches=[]
for p in sorted((E/'host').glob('K792[0-9][0-9]')):
 if not(p/'STARTED.json').exists():continue
 a=json.loads((p/'admission.json').read_text());b=json.loads((p/'barrier.json').read_text());launches.append({'id':p.name,'admission_utc':a['utc'],'outer_allowed':a['allowed'],'inner_allowed':b['allowed'],'outer_scanner_sha256':a.get('scanner_sha256'),'inner_scanner_sha256':b.get('scanner_sha256'),'launch_marker_until_retained':p.name in ['K79200','K79201']})
d['launches']=launches;d['exact_marker_snapshot_limitation']='Continuation per-launch until values were not retained. Do not infer them from the final or earlier marker. UTC/allowed receipts and scanner hashes are retained; the pinned shared scanner enforces active quiet windows. Initial K79200/K79201 marker reconstruction is separately supported by QUIET-WINDOW-AUDIT.json.';d['action']='Read-only audit; marker never edited or deleted by this task. No additional compiler/solver run, allowance exhausted.';(E/'D549-QUIET-WINDOW-AUDIT.json').write_text(json.dumps(d,indent=2)+'\n');print({'scanner_sha256':d['scanner_sha256'],'marker':d['marker'],'marker_expired_at_observation':d['marker']['until']<=d['epoch'],'scanner_hashes':sorted({x['outer_scanner_sha256']for x in launches}), 'launched_submissions':len(launches)})
