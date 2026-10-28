from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
mods=['NDE_LiftBridge','NDE_RawBridge','NDE_VariantResults','NDE_ScalarResult','NDE_LinkBridge','NDE_ClaimResult','NDE_CarryInduction','NDE_EmptyBridge','NDE_PublicBridge','NDE_PublicExt','NDE_PublicWindows','NDE_WindowIndices','NDE_RowBridge','NDE_LinearSteps','NDE_SumComposition','NDE_ReconstructTotal','NDE_PackedTotal','NDE_SimpleBridge','NDE_TerminalBridge']
s='\n'.join('import '+m for m in mods)+'\n'
for m in mods:
 for l in (E/(m+'.lean')).read_text().splitlines():
  if l.startswith('#print axioms '):
   t=l.removeprefix('#print axioms ')
   if not t.startswith('AspisR1.'):
    t=('AspisR1.' if m=='NDE_PackedTotal' else '')+m+'.'+t
   s+='#print axioms '+t+'\n'
(E/'NDE_Audit.lean').write_text(s)
code="""from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front2-20261028/NDE_objects')
print(json.dumps({str(p):dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in b.rglob('*.olean')}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
p=json.loads((E/'NDE_COHORT_PINS.json').read_text());p.update(json.loads(r.stdout));p.update({n:dict(path=n,sha256=h) for n,h in json.loads((E/'NDE_SOURCE.json').read_text())['library'].items()})
(E/'NDE_AUDIT_PINS.json').write_text(json.dumps(dict(selected_objects=p),indent=2)+'\n')
