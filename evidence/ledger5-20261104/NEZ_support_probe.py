"""Focused support-reader checks against the retained successful status layer.

Diagnostic only; final generation always replays the unchanged slice gates.
"""
import copy,json
import NEZ_validate as v
x=v.read(v.E/'NEZ_CHECKED_CANDIDATES.json')
base=v.neo.baseline()
peer=v.read(v.neo.E/'NEO_PEER_POSITIVE.json')
recipes={r['row']:r for r in peer['row_certificates']}
for rid,(lane,row) in x['candidates'].items():
    cert=x['certificates'][rid]
    if row.get('NEZ_provider')=='NET':
        row['active_support_receipts']=[]
        cert['active_support_receipts']=[]
    elif 'NEO_peer_composed_certificate' in row:
        cert['recipe']=recipes[rid]
credits={c['receipt']:copy.deepcopy(c) for c in base['NEN_credits']}
for path in v.native_refs(x['certificates']):credits[path]=v.new_credit(path,credits)
source_only=v.source_routes(x['candidates'],x['certificates'])
out=v.unify(base,x['candidates'],x['reported'],x['certificates'],credits,source_only)
print(json.dumps(dict(coverage=out['coverage'],rejected=out['NEZ_rejected_slice_closures'],source_only=sorted(source_only)),indent=2))
