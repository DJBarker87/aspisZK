"""Recompose accepted source-control bridges using the operator spines.
Only fresh modules are emitted; no existing accepted module is rewritten.
"""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh8-20261101');pins=[]
names=['LeafInstall','OpeningInstall','PrivateSaltsFlow','SaltsProver']
replacements={n:'Op'+n for n in names+['MaterialFromEntropy','ApplyMaterial','PrivateSalts','PrivateSaltStep','PrepareOpening','PublishCompact']}
for n in names:
 p=Path('lean/PV_EVH_'+n+'.lean');s=p.read_text();pins.append(dict(path=str(p),sha256=hashlib.sha256(s.encode()).hexdigest()))
 for old,new in replacements.items():s=re.sub(r'PV_EVH_'+old+r'\b','PV_EVH_'+new,s)
 if n=='PrivateSaltsFlow':
  s='import PV_EVH_OperatorFrames\n'+s
  s=s.replace('(step : PV_EVH_OpPrivateSaltStep.Callees) :\n    PV_EVH_OpPrivateSalts.Callees where','(step : PV_EVH_OpPrivateSaltStep.Callees) (frames : PV_EVH_OperatorFrames.Frames) :\n    PV_EVH_OpPrivateSalts.Callees where')
  s=s.replace('  FIBRE_COUNT_OPEN := c.FIBRE_COUNT_OPEN','  op11_OPEN := PV_EVH_OperatorFrames.map frames\n  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames\n  FIBRE_COUNT_OPEN := c.FIBRE_COUNT_OPEN')
  s=s.replace('(hs : PV_EVH_OpPrivateSaltStep.Compatible step) :','(hs : PV_EVH_OpPrivateSaltStep.Compatible step)\n    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)\n    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :')
  s=s.replace('(install fuel c step)', '(install fuel c step frames)')
  s=s.replace('  FIBRE_COUNT_fixed := hc.count_fixed','  op11_fixed := fun inst r closure => PV_EVH_OperatorFrames.map_fixed _ selected frames hf inst r closure\n  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure\n  FIBRE_COUNT_fixed := hc.count_fixed')
 if n=='SaltsProver':
  s=s.replace('import PV_EVH_ExpandedProver','import PV_EVH_OpLeafInstall')
  s=s.replace('(materialCallees : PV_EVH_OpMaterialFromEntropy.Callees)', '(materialCallees : PV_EVH_OpMaterialFromEntropy.Callees)\n    (frames : PV_EVH_OperatorFrames.Frames)')
  s=s.replace('(hmaterial : PV_EVH_OpMaterialFromEntropy.Compatible materialCallees) :', '(hmaterial : PV_EVH_OpMaterialFromEntropy.Compatible materialCallees)\n    (frame_fixed : PV_EVH_OperatorFrames.Compatible frames)\n    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :')
  s=s.replace('saltLeaves saltStep)', 'saltLeaves saltStep frames)')
  s=s.replace('hsaltLeaves hsaltStep)', 'hsaltLeaves hsaltStep frames frame_fixed selected)')
  s=s.replace('publish materialCallees)', 'publish materialCallees frames)')
 q=Path('lean/PV_EVH_Op'+n+'.lean')
 if '--check' in sys.argv:assert q.read_text()==s
 else:q.write_text(s)
record=json.dumps(dict(inputs=pins,outputs={n:hashlib.sha256(Path('lean/PV_EVH_Op'+n+'.lean').read_bytes()).hexdigest() for n in names},status='source transport; actual native association OPEN',rows_removed=[]),indent=2)+'\n';r=E/'operator-entry-generation.json'
if '--check' in sys.argv:assert r.read_text()==record
else:r.write_text(record)
print('Recomposed four source bridges; native association OPEN')
