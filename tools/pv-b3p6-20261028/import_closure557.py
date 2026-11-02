"""Freeze the exact accepted b3q sources and residual evidence, read-only upstream."""
from pathlib import Path
import subprocess,re,json,hashlib
REV='8d30a4e4004316f80341bfc72029f6b2addba66e'
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';out=R/'imports-b3q';out.mkdir(exist_ok=True)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV],text=True).splitlines()
paths={p.rsplit('/',1)[-1][:-5]:p for p in paths if p.endswith('.lean') and p.startswith('evidence/pv-b3q')}
seen=set();rows=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if m not in paths:return
 raw=subprocess.check_output(['git','show',REV+':'+paths[m]]);s=raw.decode()
 for i in re.findall(r'^import (\S+)',s,re.M):visit(i)
 p=out/'lean'/(m+'.lean');p.parent.mkdir(exist_ok=True);p.write_bytes(raw)
 rows.append(dict(module=m,path=str(p),upstream_path=paths[m],upstream_revision=REV,upstream_blob=subprocess.check_output(['git','rev-parse',REV+':'+paths[m]],text=True).strip(),sha256=hashlib.sha256(raw).hexdigest(),imports=re.findall(r'^import (\S+)',s,re.M)))
for m in ['PV_B3Q_PartialCatalogue2','PV_B3Q_D188','PV_B3Q_MatrixStore','PV_B3Q_FourSlice']:visit(m)
for group in ['pv-b3q-20261029','pv-b3q2-20261031']:
 for name in ['FINAL.md','GROUP-STATUS.md','RESIDUALS.md','catalogue-status.json','opaque-helper-status.json','d188-function-status.json','std-source-association.json','index-source-association.json']:
  path='evidence/'+group+'/'+name
  p=out/group/name
  try:raw=subprocess.check_output(['git','show',REV+':'+path],stderr=subprocess.DEVNULL)
  except subprocess.CalledProcessError:continue
  p.parent.mkdir(exist_ok=True);p.write_bytes(raw)
(R/'B3Q-SOURCE-PINS-D557.json').write_text(json.dumps(dict(revision=REV,modules=rows),indent=2)+'\n')
print(json.dumps(dict(modules=len(rows),upstream=REV)))
