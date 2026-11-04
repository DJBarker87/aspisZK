"""Replay the powers proofs on NFN's canonical field owners; no old forest import."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
old=['LPi_TowerValues','LPi_PowersStep','LPi_PowersPrefix','LPi_PowersValue','LPi_PowersSource','LPm_PowersBridge','NBQ_Powers29']
imports={n:'NFW_'+n for n in old}
imports.update({'LPi_FieldValues':'NFN_GeometryPart02','LPm_StubBounds':'NFN_GeometryPart02'})
rename={n:'NFW_'+n for n in old}
rename.update({'LPi_FieldValues':'NFN_LPi_FieldValues','LPi_CMProduct':'NFN_LPi_CMProduct','LPi_NatBase':'NFN_LPi_NatBase','LPi_Total':'NFN_LPi_Total'})
pat=re.compile(r'\b('+'|'.join(sorted(rename,key=len,reverse=True))+r')\b')
records=[]
for n in old:
 source=(R/'lean'/(n+'.lean')).read_text();body=[];imps=['Lean','NFN_PhaseTransport']
 for line in source.splitlines():
  if line.startswith('import '):
   for imp in line[7:].split():
    imp=imports.get(imp,imp)
    if imp not in imps:imps.append(imp)
  else:body.append(line)
 out=''.join('import '+x+'\n' for x in imps)+'\n'+pat.sub(lambda m:rename[m[0]],'\n'.join(body))+'\n'
 (E/('NFW_'+n+'.lean')).write_text(out)
 records.append(dict(source='lean/'+n+'.lean',sha256=hashlib.sha256(source.encode()).hexdigest(),target='NFW_'+n+'.lean',changes='imports and proof namespaces only; field/powers definitions use canonical RPz7 owner from NFN',target_sha256=hashlib.sha256(out.encode()).hexdigest()))
(E/'NFW_POWERS_PROVENANCE.json').write_text(json.dumps(records,indent=1)+'\n')
