from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;S=E.parent/'model-bridge-20261111';pins=[]
names=['RegistryOps','RegistryStd','RegistryScalarOps','RegistryFlagValues','RegistryArgs','RegistryRecordGuards','EntryRecordGuards']
for short in names:
 old='NND_'+short;new='NMX_R3_'+short;p=S/(old+'.lean');raw=p.read_text();s=raw
 for n in names:s=s.replace('NND_'+n,'NMX_R3_'+n)
 if short=='RegistryOps':
  s=s.replace('import NND_PolicyValue','import LIBB_PolicyValue').replace('import NND_BytesCarrier','import LIBB_Bytes')
 if short=='RegistryStd':
  s=s.replace('import NND_RegistryReplies','import NMX_R3_RegistryOps')
  start=s.index('theorem data');end=s.index('\ntheorem readonly');s=s[:start]+s[end:];s=s.replace('#print axioms data\n','')
 if short=='RegistryArgs':
  s=s.replace('import NND_RegistryLibrary','import RSL_TX2_234\nimport NMX_R3_RegistryCarrier')
 if short in ['RegistryArgs','RegistryRecordGuards']:
  s=re.sub(r'\baccount\b','NMX_R3_RegistryCarrier.account',s)
 (E/(new+'.lean')).write_text(s)
 pins.append(dict(source=str(p.relative_to(E.parent.parent)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),copy=new,changes='prefix names/imports only, account uses new revision3 carrier; obsolete data theorem omitted from Std, no field library construction'))
(E/'NMX_REGISTRY_HELPER_PROVENANCE.json').write_text(json.dumps(pins,indent=2)+'\n')
