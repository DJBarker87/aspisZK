#!/usr/bin/env python3
"""PCWA_regen.py STAGE BUNDLE_LOG_MAP: drive PCWA_gen_equalities.py over the module registry.
Registry (PCWA_modules.json) lists, per module, the generator arguments. STAGE 'ingest' re-runs the generator with --state (previous)
--state-out (next) --lean-log (bundle log) --bundle-offsets. Usage:
  python3 PCWA_regen.py ingest A1 probe_L001.log 1 2     # bundle A1, log, state in suffix 1, out suffix 2"""
import json,subprocess,sys
from pathlib import Path
E=Path(__file__).resolve().parent
reg=json.loads((E/'PCWA_modules.json').read_text())
stage,bundle,log,sin,sout=sys.argv[1:6]
P='../prov-p0-20261109/PCO_PARTITION.json'
for m,c in reg.items():
    if c['bundle']!=bundle:continue
    stem='PRVEq_'+m.replace('.','_')
    cmd=['python3','PCWA_gen_equalities.py','--partition',P,'--module',m,'--fresh-dir',c['fresh_dir'],'--fresh-ns',c['fresh_ns'],'--gate-source',c['gate_source'],'--out',f'eq/{stem}.lean',
         '--report',f'eq/{stem}.report.json','--state',f'eq/{stem}.state{sin}.json','--state-out',f'eq/{stem}.state{sout}.json','--lean-log',log,'--bundle-offsets',f'{bundle}_offsets.json']
    if c.get('types_source'):cmd+=['--gate-types-source',c['types_source']]
    r=subprocess.run(cmd,capture_output=True,text=True,cwd=E);print(m,r.stdout.strip()[-260:],r.stderr.strip()[-300:])
