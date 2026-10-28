from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume'
rev=subprocess.check_output(['git','rev-parse','origin/research'],text=True).strip()
branch=subprocess.check_output(['git','rev-parse','codex/pv-runjoin-20261026'],text=True).strip()
mods={};order=[]
def source(m):
 p='lean/'+m+'.lean'
 b=subprocess.run(['git','show',rev+':'+p],capture_output=True)
 if b.returncode:return None
 return p,b.stdout

def visit(m):
 if m in mods:return
 s=source(m)
 if s is None:return
 p,b=s;imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 mods[m]=dict(revision=rev,path=p,blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=imports)
 (E/'sources').mkdir(exist_ok=True);(E/'sources'/(m+'.lean')).write_bytes(b)
 for i in imports:
  if not i.startswith('XR'):visit(i)
  else:raise RuntimeError(i)
 order.append(m)
for m in ['JFx_DataPublic00','JHb_DataRequest','JFs_PublicDecode','JHu_FixturePdaRuntime','JHv_Configuration','JHb_World','JHg_World','JHe_WrapperReady','JHk_WorldFirst']:visit(m)
(E/'source-closure.json').write_text(json.dumps(dict(revision=rev,runjoin_readonly_revision=branch,modules=mods,topological=order),indent=2)+'\n')
print(len(mods),'pinned source modules; first',order[:25])
