"""Additive NFB validator; only four enumerated complete NFG roots may close."""
from pathlib import Path
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;O=E.parent/'slice-q-compose5-20261104'
# Extra immutable import path needed by NET/NEW's existing inverse audit.
sys.path.insert(0,str(E.parent/'slice-q-fnptr-20261029'));sys.path.insert(0,str(O))
import NFB_validate as prior
from NFG_certificates import packet,expected,edges as expected_edges,ROOTS
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obj=lambda p:json.loads(p.read_text())
def canonical(write=False):
 p=packet()
 if write:(E/'NFG_PACKETS.json').write_text(json.dumps(p,indent=1)+'\n')
 else:assert p==obj(E/'NFG_PACKETS.json'),'packet evidence/source/object drift'
 rows=expected(prior.prior.net.neo.baseline(),p)
 if write:(E/'NFG_CERTIFICATES.json').write_text(json.dumps(rows,indent=1)+'\n')
 else:assert rows==obj(E/'NFG_CERTIFICATES.json'),'root certificate drift'
 out,new=expected_edges(obj(O/'NFB_EDGES.json'),p)
 return rows,out,new

def validate(edges=None,certificates=None,replay=False,write=False):
 old=prior.validate(replay=replay)
 assert old==obj(O/'NFB_LEDGER_DELTA.json'),'inherited NFB result drift'
 rows,wanted,new=canonical(write=write)
 certificates=obj(E/'NFG_CERTIFICATES.json') if certificates is None else certificates
 assert certificates==rows,'unregistered/incomplete root certificate'
 if write:(E/'NFG_EDGES.json').write_text(json.dumps(wanted,indent=1)+'\n')
 edges=obj(E/'NFG_EDGES.json') if edges is None else edges
 assert edges==wanted,'unregistered edge change, prune or hidden closure'
 roots=dict(old['roots']);roots.update({root:'CLOSED' for root in ROOTS})
 return dict(schema='NFG-additive-NFB-v1',baseline_validator_sha256=sha(O/'NFB_validate.py'),validator_sha256=sha(E/'NFG_validate.py'),newly_closed=sorted(r['row'] for r in rows),new_count=len(rows),new_functions=sorted(ROOTS),total_closed=old['total_closed']+len(rows),q_occurrences_closed=old['q_occurrences_closed']+len(rows),q_functions_closed=old['q_functions_closed']+len(ROOTS),edge_closed=old['edge_closed']+len(new),edge_total=old['edge_total'],new_edges=new,roots=roots,trust=old['trust'],security_target_established=False,packet_sha256=sha(E/'NFG_PACKETS.json'),certificates_sha256=sha(E/'NFG_CERTIFICATES.json'),inherited_qualification='Source-validator NFB geometry count retained; NEW/NFB Phase-owner conflict against RPx is unresolved. Four new roots import coherently with RPx (NFG_L077); this is not a combined headline release proof.',no_credit=['four_dots_one','four_dots','query_values','query_loop','inverse G windows','generic inv_with'],transport='P6/D188 option A trust reclassification, not removal')
if __name__=='__main__':
 write='--write' in sys.argv;d=validate(replay='--replay' in sys.argv,write=write)
 if write:(E/'NFG_LEDGER_DELTA.json').write_text(json.dumps(d,indent=1)+'\n')
 else:assert d==obj(E/'NFG_LEDGER_DELTA.json'),'ledger drift'
 print(json.dumps(d))
