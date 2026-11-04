import json
import NFD_validate as v
import NFD_raw_checks as c
from NFD_build_certificates import theorem
from NFD_composition_support import make
E=v.E
if __name__=='__main__':
 packet=v.read(E/'NFD_LEDGER_DELTA.json');base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',trust_rows=[])
 for f in [c.LIMBS,c.TAG]:
  attempts=['NFD_K127','NFD_K128'] if f==c.LIMBS else ['NFD_K129','NFD_K130']
  domain='every raw eight-u32 WideExact carrier; no canonicality restriction' if f==c.LIMBS else 'all three Variant constructors'
  n=dict(function=f,complete=True,domain=domain,pairs=[attempts]);thms=[theorem(t,'NFD_L036') for t in c.THMS[f]]
  resolved=v.compose(base,packet);cert=make(f,n,thms,resolved,attempts,['NFD_RAW_SOURCE_DIGESTS.json'],c.CLASS)
  assert v.certificate(cert,f,resolved)
  packet['NFD_certificates'][f]=cert
 out=v.compose(base,packet);assert all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function'] in [c.LIMBS,c.TAG])
 (E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n')
 print(sum(r['composed_status']=='CLOSED' for r in out['rows']))
