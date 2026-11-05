"""Inventory supplied NIG exports, without adding a replacement specification."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-pair4-20261107'
records=['Common','Low','Final','LibraLog','SameGuard','Initial','PairEdges','NewPort','PairPort','FinishLog']
rows=[]
for p in sorted(P.glob('*.lean')):
 s=p.read_text();rows.append(dict(path=str(p.relative_to(E.parent.parent)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declarations=[dict(kind=k,name=n)for k,n in re.findall(r'^(?:noncomputable\s+)?(structure|inductive|def|abbrev|theorem)\s+(\w+)',s,re.M)]))
found={r:[dict(path=x['path'],declaration=d)for x in rows for d in x['declarations']if d['name']==r]for r in records}
assert not any(found.values()),found
(E/'NIQ_INTERFACE_INVENTORY.json').write_text(json.dumps(dict(scope='Supplied NIG top-level .lean exports; no claim of universal impossibility',records_requested=records,matching_exported_carriers=found,exports=rows,classification='missing typed local-record interpretation; model equations exist'),indent=2)+'\n')
print('NIG exported model laws inventoried; no matching native-record carriers')
