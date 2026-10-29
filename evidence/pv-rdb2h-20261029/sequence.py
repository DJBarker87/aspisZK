from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;p=json.loads((E/'plan.json').read_text());assert len(p['continuation_order'])==48
for i,m in enumerate(p['continuation_order']):
 n={'R1Z.PV_RDB2F_StatementAudit':64397,'R1Z.PV_RDB2F_AxiomsAudit':64398,'R1Z.PV_RDB2F_FocusedReplay':64399}.get(m,64300+i)
 r=subprocess.run([sys.executable,str(E/'lean.py'),str(n),m])
 if r.returncode:sys.exit(r.returncode)
