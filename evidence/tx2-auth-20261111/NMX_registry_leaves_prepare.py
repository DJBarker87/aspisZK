from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;S=E.parent/'model-bridge-20261111'
for i in [1,2]:
 args='(ops : Ops) (v p : solana_pubkey.Pubkey) '
 if i==1:
  args+='(e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (expected : solana_pubkey.Pubkey)'
  body='NMX_R3_RegistryNativeParts.native018 ops v e t p r expected'
 else:
  args+='(t : U64) (loader : Array U8 32#usize) (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (expected : solana_pubkey.Pubkey)'
  body='NMX_R3_RegistryNativeParts.native011 ops v t loader p r expected'
 s='import NMX_R3_RegistryNativeParts\nimport NMX_R3_RegistryScalarOps\nimport NMX_R3_EntryRecordGuards\n'+('import NMX_R3_EntryV2Guard\n' if i==2 else '')+'''set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEntry%dCheck
open Aeneas Aeneas.Std AdapterRw
'''%i+'def check '+args+' := '+body+'\nend NMX_R3_RegistryEntry%dCheck\nend\n'%i
 (E/('NMX_R3_RegistryEntry%dCheck.lean'%i)).write_text(s)
names=['RegistryOps','RegistryStd','RegistryScalarOps','RegistryFlagValues','RegistryArgs','RegistryRecordGuards','EntryRecordGuards','EntryV2Guard','RegistryEntry1Check','RegistryEntry2Check','RegistryEntry1Value','RegistryEntry2Value']
pins=json.loads((E/'NMX_REGISTRY_HELPER_PROVENANCE.json').read_text())
for name in ['EntryV2Guard','RegistryEntry1Value','RegistryEntry2Value']:
 p=S/('NND_'+name+'.lean');raw=p.read_text();s=raw
 for n in names:s=s.replace('NND_'+n,'NMX_R3_'+n)
 if name=='EntryV2Guard':s=re.sub(r'\baccount\b','NMX_R3_RegistryCarrier.account',s)
 if name.startswith('RegistryEntry'):
  i=int(name[len('RegistryEntry')]);n='018' if i==1 else '011'
  s=s.replace('simp only [NMX_R3_RegistryEntry%dCheck.check,'%i,'simp only [NMX_R3_RegistryEntry%dCheck.check, NMX_R3_RegistryNativeParts.native%s,'%(i,n))
 (E/('NMX_R3_'+name+'.lean')).write_text(s)
 pins.append(dict(source=str(p.relative_to(E.parent.parent)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),copy='NMX_R3_'+name,changes='prefix/import names; current account carrier; exact literal native leaf behind checked wrapper'))
(E/'NMX_REGISTRY_HELPER_PROVENANCE.json').write_text(json.dumps(pins,indent=2)+'\n')
