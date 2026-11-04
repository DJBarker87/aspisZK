"""Attach newly checked explicit constant/domain facts to the validated packet.
Full inherited CLI replay remains mandatory and unchanged; this updates proof
references only, using the already validated exact row snapshot.
"""
import json
import NEY_validate as v
import NEY_build_certificates as build
import NEY_bridge_checks as b
E=v.E
packet=v.read(E/'NEY_LEDGER_DELTA.json');c=packet['NEY_certificates'][b.TERMINAL]
c['geometry_theorems']=[build.theorem('NEY_TerminalGeometry.'+name,'NEY_L035',E,'NEY_') for name in ['payment_offset','header_constants','kind_same','payment_window']]
c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
base={'frozen_revision':c['frozen_revision'],'rows':v.read(E/'NEY_CHECKED_ROWS.json')}
assert v.certificate(c,b.TERMINAL,base)
(E/'NEY_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n')
print('Existing terminal certificate strengthened with four checked geometry facts; no count changed')
