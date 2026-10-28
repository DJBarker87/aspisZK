"""Preserve uncertain submission49, check host read-only, continue without replay."""
from KNA_runtime import *
import datetime
attempt='KNA_K049'
assert not (E/attempt/'receipt.json').exists()
assert not any(x['name']=='body_480_560' for x in json.loads((E/'KNA_PAIRS.json').read_text()))
code='''from pathlib import Path
import json,subprocess
b=Path('''+repr(t.B)+''')
rows=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines()
live=[x for x in rows if x.split(None,1)[1].startswith('python3 S2W_run_host.py KNA_') or (x.split(None,1)[1].split()[0].endswith('/kani-driver') and 'KNA_windows' in x)]
p=b/'KNA_K049'
print(json.dumps(dict(live=live,attempt_directory_exists=p.exists(),receipt_exists=(p/'receipt.json').exists()),indent=2))
'''
r=t.remote_py(code);assert r.returncode==0,r.stderr;rec=json.loads(r.stdout)
assert not rec['live'],rec
assert not rec['receipt_exists'] and not rec['attempt_directory_exists'],'Recover read-only; do not continue until existing attempt is classified'
source=BASE+ATTR+'fn KNA_body_480_560(){'+bodywindow(480,560)+'}\n'
sha=hashlib.sha256(source.replace('NEG','0u8').encode()).hexdigest();assert (E/'sources'/(sha+'.rs')).exists()
rec.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),result='UNRESOLVED',budget_charge=1,source_sha256=sha,policy='No terminal receipt after10 recovery polls; read-only no-live check; never resubmit this shape; count admission conservatively.')
(E/'KNA_K049_RECOVERY.json').write_text(json.dumps(rec,indent=2)+'\n')
assert len(list(E.glob('KNA_K[0-9][0-9][0-9].json')))==49
negative=invoke('body_480_560',source,True,attempt)
rows=json.loads((E/'KNA_PAIRS.json').read_text());rows.append(dict(name='body_480_560',positive='UNRESOLVED',control=negative,positive_id=attempt,control_id='KNA_K050',credit=False));(E/'KNA_PAIRS.json').write_text(json.dumps(rows,indent=2)+'\n')
if negative in ['PASS','ERROR']:raise SystemExit('Inspect K050 control '+negative)
from KNA_resume import main
main()
