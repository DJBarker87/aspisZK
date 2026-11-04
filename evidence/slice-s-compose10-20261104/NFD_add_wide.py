import json
import NFD_validate as v
import NFD_wide_checks as c
from NFD_build_certificates import theorem
from NFD_composition_support import make,seal
E=v.E
if __name__=='__main__':
 packet=v.read(E/'NFD_LEDGER_DELTA.json');base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',trust_rows=[])
 resolved=v.compose(base,packet);thms=[theorem(t,'NFD_L037') for t in c.THMS]
 n=dict(function=c.F,complete=True,domain=c.DOMAIN,step=c.ATTEMPTS,callee='crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs')
 cert=make(c.F,n,thms,resolved,c.ATTEMPTS,c.EXTRAS,c.CLASS);cert['resolved_non_calls']=c.RESOLVED;seal(cert)
 assert v.certificate(cert,c.F,resolved)
 packet['NFD_certificates'][c.F]=cert;out=v.compose(base,packet)
 assert all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==c.F)
 (E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n')
 print(sum(r['composed_status']=='CLOSED' for r in out['rows']))
