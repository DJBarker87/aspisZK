"""Refresh only own tracked sources; require every dependency already resolved.
External and EJR/freeze authorities remain untouched.
"""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d355'
p=E/'focused-resolution.json';q=E/'focused-project-sources.json'
r=json.loads(p.read_text());s=json.loads(q.read_text());head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for m in sys.argv[1:]:
 path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 old=r['resolved'].get(m)
 assert old is None or old['authority']=='h5 own git-tracked HEAD',m
 b=subprocess.check_output(['git','show',head+':'+path]);body=b.decode()
 imports=[n for line in re.findall(r'^\s*(?:(?:public|private)\s+)?import[ \t]+([^\n]+)',body,re.M) for n in line.split()]
 assert all(d in r['resolved'] for d in imports),imports
 r['resolved'][m]=dict(authority='h5 own git-tracked HEAD',path=path,git_blob=subprocess.check_output(['git','rev-parse',head+':'+path],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=imports,tracked_conflicts=[])
 s[m]=body
r['head']=head;p.write_text(json.dumps(r,indent=2)+'\n');q.write_text(json.dumps(s)+'\n')
