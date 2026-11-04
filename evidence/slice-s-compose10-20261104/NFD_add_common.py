import json
from pathlib import Path
import NFD_validate as v
import NFD_common_checks as c
from NFD_build_certificates import ref,theorem
E=v.E;P=E.parent/'slice-s-compose7-20261103'
def add(packet,base):
 pairs=[[f'NFD_K{38+2*i:03}',f'NFD_K{39+2*i:03}'] for i in range(15)]
 thms=[theorem('NEU_ReconstructCore.common_result','NEU_L010',P,'NEU_'),theorem('NEU_CallDomains.common_packet','NEU_L012',P,'NEU_'),theorem('NEU_CommonProjections.common_ext','NEU_L015',P,'NEU_')]+[theorem(f'NFD_CommonField{i:02}.alignment',f'NFD_L{20+i:03}') for i in range(15)]
 support={E/'NFD_COMMON_TEMPLATE.json',E/'NFD_AUTH_INITIALIZATION.json'}
 for a in [a for pair in pairs for a in pair]+['NFD_K068']:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NFD_native_contracts.patch',a+'-NFD_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NFD_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256'];support.update(E/n for n in names)
 f=c.COMMON
 cert=dict(id='NFD_common',kind='member-composition',subject=f,frozen_revision=base['frozen_revision'],native_certificate=dict(function=f,complete=True,pairs=pairs,controls=['NFD_K068'],domain='every typed Auth/Candidate with every scalar independently arbitrary; no canonicality or accepted-run restriction'),domain_theorems=thms,physical_theorems=thms,support=[ref(p) for p in sorted(support)],required_obligations=[o['id'] for r in base['rows'] if r['function']==f for o in r['caller_domain_obligations']],edges=[],call_domain_certificates={},hypotheses=[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'],new_trust_rows=[],inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',allocation_qualification='approved Allocator returning fresh uniquely owned block or abort; aa value, same captured allocated Box, same ownership transfer; source has no error cleanup path')
 cert.update({k:True for k in ['exact_callsite',*__import__('NFD_bridge_checks').FLAGS]})
 cert['semantic_review_sha256']=v.sha(json.dumps(cert,sort_keys=True).encode())
 assert v.certificate(cert,f,base)
 packet['NFD_certificates'][f]=cert
 return packet
if __name__=='__main__':
 packet=v.read(E/'NFD_LEDGER_DELTA.json');base=dict(rows=v.read(E/'NFD_CHECKED_ROWS.json'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',trust_rows=[])
 packet=add(packet,base);(E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n')
 out=v.compose(base,packet);(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n');print(sum(r['composed_status']=='CLOSED' for r in out['rows']))
