from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2];D='/home/dombarker/project-offloads/codex-pv-rdb2-20261028';E=R/'evidence/pv-rdb2-20261028'
for suite,kind in [('sum','project'),('sampler','project'),('weights','project'),('sha','dep'),('ct','dep')]:
 name='native-'+suite
 cmd=[sys.executable,str(R/'tools/pv-rdb2-20261028/scope.py'),name,'release compilation then finite same-input '+suite+' differential','python3',D+'/classify-'+kind+'-native.py',suite]
 with (E/(name+'-driver.log')).open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 print(name,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
