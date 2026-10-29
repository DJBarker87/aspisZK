from pathlib import Path
import re,json,subprocess,hashlib
P=Path(__file__).parent;rows=json.loads((P/'claim-recorded-audits.json').read_text());cache={}
def get(ref,path):
 k=(ref,path)
 if k not in cache:
  r=subprocess.run(['git','show',ref+':'+path],capture_output=True);cache[k]=r.stdout if not r.returncode else None
 return cache[k]
def norm(a):return re.sub(r'\.\{[^}]*\}$','',a)
for row in rows:
 for a in row['recorded_audits']:
  a['axioms_normalized']=[norm(x)for x in a['axioms']];a['nonstandard']=[x for x in a['axioms_normalized']if x not in ['propext','Classical.choice','Quot.sound']]
  ref,path=a['ref'],a['path'];p=Path(path);n=re.search(r'(?:lean-?|out-|output-|[/-])(\d{5})(?:[./-]|$)',path)
  id=n[1]if n else None
  paths=[path]if path.endswith('.json')else[]
  paths += [str(p.parent/'receipt.json'),str(p.parent/'receipt/receipt.json')]
  if id:paths += [str(p.parent/(id+'.json')),str(p.parent/(id+'-receipt.json')),str(p.parent/('lean-'+id)/'receipt.json'),str(p.parent/('lean-'+id)/'receipt/receipt.json')]
  a['attempt']=id;a['receipt_status']=[]
  for q in dict.fromkeys(paths):
   data=get(ref,q)
   if not data:continue
   try:o=json.loads(data)
   except Exception:continue
   if not isinstance(o,dict):continue
   status={k:o[k]for k in ['exit','exit_status','lean_exit','validation_exit','source_sha256','source_revision','module','target']if k in o}
   if status:a['receipt_status'].append(dict(path=q,sha256=hashlib.sha256(data).hexdigest(),**status))
  a['diagnostic_class']='nonstandard historical output (not credited)'if a['nonstandard']else'standard-only output'
 row['nonstandard_audits']=[a for a in row['recorded_audits']if a['nonstandard']]
 good=[a for a in row['recorded_audits']if not a['nonstandard']]
 # Prefer exact exit-zero receipt evidence; retained logs still exposed if status unknown.
 def rank(a):
  verified=any((s.get('exit_status',s.get('lean_exit',s.get('exit')))==0)for s in a['receipt_status'])
  return verified, int(a['attempt']or 0),a['path'].endswith('.log')
 good.sort(key=rank,reverse=True);row['selected_standard_audit']=good[0]if good else None
 row['verdict']='standard-only closing audit located; rejected/historical failures kept separate'if good else'no closing theorem (inventory audit row)'if row['id']=='V270'else'NO STANDARD-ONLY CLOSING AUDIT'
(P/'claim-audit-dispositions.json').write_text(json.dumps(rows,indent=1));print('standard',sum(x['selected_standard_audit']is not None for x in rows),'nonstandard histories',[(x['id'],len(x['nonstandard_audits']))for x in rows if x['nonstandard_audits']]);print('verified receipts',sum(any(s.get('exit_status',s.get('lean_exit',s.get('exit')))==0 for s in (x['selected_standard_audit']or{}).get('receipt_status',[]))for x in rows))
