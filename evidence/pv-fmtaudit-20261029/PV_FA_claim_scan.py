from pathlib import Path
import subprocess,json,re,hashlib
P=Path(__file__).parent
rows=json.loads((P/'credited-row-input.json').read_text());pins=json.loads((P/'input-recount9-pins.json').read_text())['revisions']
refs=list(dict.fromkeys(['bbedfc018d67a8fa6208627e199ee336b628c17e',pins['rw'],pins['cb'],pins['cb3'],pins['cbmid'],pins['cblib'],pins['b3p6'],pins['rdcd3']]))
terms=[x['closure_theorem']for x in rows if x.get('closure_theorem')];patterns=P/'PV_FA_patterns.txt';patterns.write_text('\n'.join(terms)+'\n')
found={t:[]for t in terms};index=[]
regex=re.compile(r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",re.M)
for ref in refs:
 out=subprocess.run(['git','grep','-l','-F','-f',str(patterns),ref,'--','*.log','*.txt','*.json'],capture_output=True,text=True)
 files=out.stdout.splitlines();print(ref[:10],len(files),flush=True)
 for f in files:
  data=subprocess.check_output(['git','show',f]);text=data.decode(errors='replace')
  # Receipts often encode newlines and quotes as JSON strings.
  texts=[text]
  if f.endswith('.json'):
   try:
    obj=json.loads(text)
    def strings(o):
     if isinstance(o,str):yield o
     elif isinstance(o,list):
      for v in o:yield from strings(v)
     elif isinstance(o,dict):
      for v in o.values():yield from strings(v)
    texts+=list(strings(obj))
   except Exception:pass
  for tx in texts:
   for m in regex.finditer(tx):
    name=m[1]
    if name not in found:continue
    axs=[x.strip()for x in (m[2]or'').replace('\n',' ').split(',')if x.strip()]
    entry=dict(ref=ref,path=f.split(':',1)[1],sha256=hashlib.sha256(data).hexdigest(),theorem=name,output=m[0],axioms=axs,nonstandard=[a for a in axs if a not in ['propext','Classical.choice','Quot.sound']])
    if not any(x['ref']==ref and x['path']==entry['path']and x['output']==entry['output']for x in found[name]):found[name].append(entry)
result=[]
for row in rows:
 t=row.get('closure_theorem');a=found.get(t,[])
 result.append(dict(id=row['id'],theorem=t,status8=row.get('recount8_status'),status9=row.get('recount9_status'),recorded_audits=a,nonstandard_audits=[x for x in a if x['nonstandard']],verdict='recorded standard-only output located'if a and not any(x['nonstandard']for x in a)else'nonstandard output'if a else'NO EXACT CLOSING-THEOREM OUTPUT LOCATED'))
(P/'claim-recorded-audits.json').write_text(json.dumps(result,indent=1))
print('located',sum(bool(x['recorded_audits'])for x in result),'of',len(result));print('missing',[x['id']for x in result if not x['recorded_audits']]);print('nonstandard',[(x['id'],len(x['nonstandard_audits']))for x in result if x['nonstandard_audits']])
