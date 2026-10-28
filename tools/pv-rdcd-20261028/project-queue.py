from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for suite in ['circle','weights','bytes','arithmetic','leaves']:
 r=subprocess.run([sys.executable,str(R/'tools/pv-rdcd-20261028/scope.py'),'native-'+suite,'optimized compilation then original '+suite+' finite differential','python3','/home/dombarker/project-offloads/codex-pv-rdcd-20261028/native-project.py',suite],capture_output=True,text=True)
 (R/'evidence/pv-rdcd-20261028'/('native-'+suite+'-dispatch.log')).write_text(r.stdout+r.stderr)
 print(suite,r.returncode,(r.stdout+r.stderr)[-350:],flush=True)
 if r.returncode:sys.exit(r.returncode)
