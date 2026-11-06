from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
pairs=[(4,2),(5,6),(9,8),(15,16),(19,20),(17,18),(28,27),(29,30),(31,32),(25,26),(35,36),(33,34),(37,38),(43,44),(49,50),(47,48),(51,52),(53,54),(55,56),(57,58),(59,60),(61,62)]
rows=[]
for p,n in pairs:
 a,b=f'NJL_K{p:03}',f'NJL_K{n:03}';receipts=[]
 for attempt,expected in[(a,0),(b,1)]:
  r=json.loads((E/attempt/'receipt.json').read_text());s=(E/attempt/'stdout.log').read_text();g=json.loads((E/(attempt+'-graph-check.json')).read_text());lock=json.loads((E/(attempt+'-lock-check.json')).read_text())
  assert r['exit_status']==expected and 'Verification Time' in s and 'CBMC timed out'not in s and 'timed out'not in s,attempt
  assert g['graph_matches_frozen'] and lock['unchanged'],attempt
  receipts.append(r)
 x,y=receipts
 common=set(x['source_hashes'])&set(y['source_hashes']);diff=[k for k in common if x['source_hashes'][k]!=y['source_hashes'][k]]
 rows.append(dict(positive=a,negative=b,positive_exit=0,negative_exit=1,both_reach_verification=True,graph_frozen=True,lock_unchanged=True,common_input_differences=diff,positive_receipt=a+'/receipt.json',negative_receipt=b+'/receipt.json'))
extra='NJL_K063';r=json.loads((E/extra/'receipt.json').read_text());s=(E/extra/'stdout.log').read_text();assert r['exit_status']==1 and'Verification Time'in s and'CBMC timed out'not in s
(E/'NJL_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows,extra_negative=extra,extra_credit=False,kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'),indent=2)+'\n')
print(json.dumps(dict(verified_pairs=len(rows),extra_negative=extra,input_difference_pairs=[r['positive']for r in rows if r['common_input_differences']])))
