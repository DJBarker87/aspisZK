"""Source authority audit for the four frozen extraction dependencies only."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
rev=git('rev-parse','HEAD').decode().strip()
j=json.loads((R/'evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_bytes())
pins={x['module'].replace('/','.') for x in j['selected'] if x.get('resolution')}
f=json.loads((R/'docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json').read_bytes())
frozen={x['module'].replace('/','.') for x in f['sources']}
rows=[]
for suf in ['ExternalTypes','Types','ExternalFuns','Funs']:
 m='R1Z.ProverRwFull'+suf;p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFull'+suf+'.lean'
 assert m not in pins and m not in frozen,(m,'must use earlier authority')
 b=git('show','HEAD:'+p);assert (R/p).read_bytes()==b
 rows.append(dict(module=m,path=p,revision=rev,blob=git('rev-parse','HEAD:'+p).decode().strip(),sha256=hashlib.sha256(b).hexdigest(),imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M),authority='h5 tracked HEAD; absent from EJR/freeze',reuse=False))
(E/'extraction-dependencies.json').write_text(json.dumps(rows,indent=2)+'\n')
print([(r['module'],r['sha256']) for r in rows])
