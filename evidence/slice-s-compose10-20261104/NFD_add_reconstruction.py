import NFD_validate as v
import NFD_reconstruction_checks as c
from NFD_build_certificates import theorem
from NFD_composition_support import make
import json
E=v.E;P=E.parent/'slice-s-compose7-20261103'
if __name__=='__main__':
 packet=v.read(E/'NFD_LEDGER_DELTA.json');base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',trust_rows=[])
 thms=[theorem(n,{'NEU_ReconstructCore':'NEU_L010','NEU_ReconstructAdopted':'NEU_L011','NEU_CallDomains':'NEU_L012'}[n.split('.')[0]],P,'NEU_') for n in c.THMS]
 n=dict(function=c.F,complete=True,domain='all typed Request/Auth/Candidate; raw noncanonical fields admitted; no accepted-run condition',prefix=['NFD_K085','NFD_K086'],pairs=[[f'NFD_K{91+2*i:03}',f'NFD_K{92+2*i:03}'] for i in range(9)],controls=['NFD_K109','NFD_K110'])
 resolved=v.compose(base,packet)
 cert=make(c.F,n,thms,resolved,c.ATTEMPTS,c.EXTRAS,c.CLASS)
 assert v.certificate(cert,c.F,resolved),'certificate rejected'
 packet['NFD_certificates'][c.F]=cert
 out=v.compose(base,packet)
 assert all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==c.F)
 (E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n')
 print(sum(r['composed_status']=='CLOSED' for r in out['rows']))
