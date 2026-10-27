"""Static preflight for the resumed proof closure; no compiler or host scope."""
from pathlib import Path
import subprocess,json,re,hashlib
root=Path(__file__).resolve().parents[2];e=root/'evidence/pv-cb3-20261026';lean=root/'docs/research/v8-r0-zk-20261009/lean'
old=json.loads((e/'bundle-replay-plan.json').read_text())['order']
added=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_*.lean'],cwd=root,text=True).splitlines()
changes=subprocess.check_output(['git','diff','--name-only','54f2ac877f','--','*.lean'],cwd=root,text=True).splitlines()
old_changed=[]
for p in changes:
 x=subprocess.run(['git','cat-file','-e','54f2ac877f:'+p],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 if x.returncode==0:old_changed.append(p)
receipts={}
for p in e.glob('35*.json'):
 if re.fullmatch(r'35[678]\d\d\.json',p.name):
  r=json.loads(p.read_text())
  if 'axioms' in r and 'module' in r:receipts.setdefault(r['module'].replace('/','.'),[]).append(r)
allnew=[p for p in lean.glob('R1Z/PV_CB3_*.lean') if subprocess.run(['git','cat-file','-e','54f2ac877f:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode]
checks=[];forbidden=[]
for p in allnew:
 s=p.read_text();m='R1Z.'+p.stem;sha=hashlib.sha256(s.encode()).hexdigest();good=[r for r in receipts.get(m,[]) if r['exit']==0 and r['source_sha256']==sha]
 bad=re.findall(r'(?m)^\s*(?:axiom\b|.*\b(?:sorry|admit|native_decide|implemented_by)\b)',s)
 if bad:forbidden.append({'module':m,'lines':bad})
 checks.append({'module':m,'source_sha256':sha,'checked_receipts':[r['attempt'] for r in good],'pending':not bool(good)})
r=dict(base='54f2ac877f',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),existing_lean_modules_changed=old_changed,forbidden=forbidden,original_manifest=old,new_module_checks=checks,charged_lean=sum(map(len,receipts.values())),pending=[x['module'] for x in checks if x['pending']],scope='Source/body/manifest preflight only; not a proof replay or privacy endpoint closure.')
(e/'RESUME_PREFLIGHT.json').write_text(json.dumps(r,indent=2)+'\n');print('Existing modules changed:',old_changed,'forbidden:',forbidden,'pending:',r['pending'])
assert not old_changed and not forbidden
