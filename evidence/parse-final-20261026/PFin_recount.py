#!/usr/bin/env python3
"""Reviewed source-instance correspondence, using the Rc2 atomic-leaf ledger.
This is an audit renderer, not a logical discharge checker. Proof evidence is
PFin_Audit and PFin_Final.accepted. It preserves the source-specialization
qualification rather than asserting the universal predecessor was weakened.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
root=Path(__file__).resolve().parents[2]
base=root/'evidence/recount2-20261026/Rc2_premises.json'
x=json.loads(base.read_text())
removed={'L099','L129','L130','L131','L132',*(f'N{n}' for n in range(108,115))}
rows=x['rows'];present={r['id'] for r in rows}
assert removed<=present
changed=[{**r,'status':'source instance derived','proof':('PFin_Packet.from_cut / F3L_PreparedPort.from_cut' if r['id']!='L099' else 'PFin_BoundCaller.from_cut'),'qualification':'Fixed SAME accepted source transcript/data, not every arbitrary tr/i.'} for r in rows if r['id'] in removed]
after=[r for r in rows if r['id'] not in removed]
def count(rs,scope=None):
 rs=[r for r in rs if scope is None or r['scope']==scope]
 return {'classification':dict(sorted(Counter(r['classification'] for r in rs).items())), 'owner':dict(sorted(Counter(r['owner'] for r in rs).items()))}
scopes=['actual antecedent','deployment only','deployment alias']
def totals(rs):
 return {**{scope:count(rs,scope) for scope in scopes},'all retained audit rows':count(rs),'deduplicated actual plus non-alias deployment':count([r for r in rs if r['scope']!='deployment alias'])}
paths=['lean/Rc2_Top.lean','lean/PFin_Top.lean','lean/PFin_FinalResult.lean','lean/PFin_BoundCaller.lean','lean/PFin_Cont.lean','lean/PFin_Packet.lean','lean/PFin_Finish.lean','lean/PFin_Ten.lean']
out={'before_theorem':'AspisR1.Rc2_Top.deployed','after_theorem':'AspisR1.PFin_Top.deployed','baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'method':x['method'],'before':totals(rows),'after':totals(after),'removed':changed,'added':[], 'retained_N115':next(r for r in after if r['id']=='N115'),'requested_sites':['L099','L129','L130','L131','L132','WhenBound.parseReached (includes Aligned)','WhenBound.read'],'alias_note':'Seven requested sites map to five existing independent ledger IDs; pure WhenBound is not in Rc2_Result. Never subtract two extra rows. N108-N114 are seven additional atomic preparation leaves.','quantifiers':'The new result fixes semantic/q/tr/i to derived source values; generic arbitrary-instance lemmas remain supporting theorems. No root hypotheses, game, failure event, runtime trust, carrier type or headline conclusion changed. This is source instantiation, not universal transcript generation.','nonvacuity':'PFin_Packet exists before history/P2Prime/geometry leaves; PFin_Final.accepted has no headline/raw/binding inputs. Full joint retained-interface satisfiability remains unproved. Frozen2 headline must not be presented as the adopted frozen3 release theorem.','source_sha256':{p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}}
(root/'evidence/parse-final-20261026/PFin_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'before':out['before'],'after':out['after'],'removed':[r['id'] for r in changed]},indent=2))
