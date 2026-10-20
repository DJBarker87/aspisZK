#!/usr/bin/env python3
"""Copy small historical receipts, with hashes for retained large logs and ELFs."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parents[1];H='/home/dombarker/project-offloads/codex-cx-stage2b-20261020';remote='dombarker@100.108.41.90'
for tag in sys.argv[1:]:
 d=E/'historical-runtime'/tag;d.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp',remote+':'+H+'/cu-'+tag+'.json',str(d/'cu.json')],check=True)
 subprocess.run(['scp','-r',remote+':'+H+'/receipts/'+tag+'-*',str(d)],check=True)
 import json
 j=json.loads((d/'cu.json').read_text());failed=[r['fixture'] for r in j['rows'] if not(r['outcome']=='accepted' and r['stage1_ok'] and r['settlement_ok'])]
 (d/'gate-status.json').write_text(json.dumps(dict(full_gate_exit_status=1 if failed else None,stopped_on_cu_failure=failed,cu_fixtures_completed=len(j['rows']),full_six_fixture_gate_passed=len(j['rows'])==6 and not failed,remaining_gates_not_started_due_to_stop=bool(failed)),indent=2)+'\n')
