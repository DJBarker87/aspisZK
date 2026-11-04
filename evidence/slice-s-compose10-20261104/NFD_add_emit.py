import NFD_validate as v
import NFD_emit_checks as c
from NFD_build_certificates import theorem
from NFD_composition_support import make
import json
E=v.E;P=E.parent/'slice-s-compose9-20261104'
if __name__=='__main__':
 packet=v.read(E/'NFD_LEDGER_DELTA.json');base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',trust_rows=[])
 thms=[theorem(n,'NEY_L041',P,'NEY_') if n.startswith('NEY_') else theorem(n,'NFD_L035') for n in c.THMS]
 n=dict(function=c.F,complete=True,domain=c.DOMAIN,pairs=[[f'NFD_K{111+2*i:03}',f'NFD_K{112+2*i:03}'] for i in range(8)],continuation=['NFD_K087','NFD_K088','NFD_K089','NFD_K090'])
 resolved=v.compose(base,packet);cert=make(c.F,n,thms,resolved,c.ATTEMPTS,c.EXTRAS,c.CLASS,['RuntimeReturnData'])
 assert v.certificate(cert,c.F,resolved),'certificate rejected'
 packet['NFD_certificates'][c.F]=cert;out=v.compose(base,packet)
 assert all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==c.F)
 (E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n')
 print(sum(r['composed_status']=='CLOSED' for r in out['rows']))
