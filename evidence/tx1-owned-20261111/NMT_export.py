from NMT_formal import *
files={n:(E/n).read_text()for n in ['NMT_export_host.py','NMT_CURRENT_MODULES.json']}
r=run('NMT_L060','inspect','NMT_final_export',['python3','NMT_export_host.py'],extra=files)
if r['exit_status']:raise SystemExit(r['exit_status'])
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text()for n in ['NMT_EXPORT.json','NMT_AENEAS_PINS.json','NMT_RETENTION.json']}}))
''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():(E/n).write_text(s)
print('NMT final own export and retention recovered',flush=True)
