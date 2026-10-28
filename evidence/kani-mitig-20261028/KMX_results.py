from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
rows=[]
for d in sorted(E.glob('KMX_*/stdout.log')):
 t=d.read_text()
 ms=list(re.finditer(r'Checking harness ([^\n]+?)\.\.\.',t))
 for i,m in enumerate(ms):
  part=t[m.end():ms[i+1].start() if i+1<len(ms) else len(t)]
  results=re.findall(r'VERIFICATION:- (SUCCESSFUL|FAILED)',part)
  result=({'SUCCESSFUL':'PASS','FAILED':'FAIL'}[results[-1]] if results else 'TIMEOUT' if re.search('timed out|TIMEOUT',part,re.I) else 'INCOMPLETE')
  if re.search(r'CBMC timed out|TIMEOUT',part,re.I):result='TIMEOUT'
  if result=='INCOMPLETE' and json.loads((d.parent/'receipt.json').read_text()).get('exit_status')==124:result='TIMEOUT'
  failed=[]
  for c in re.split(r'(?=Check \d+:)',part):
   if 'Status: FAILURE' in c:
    failed.append(c.split('\n\n')[0].strip())
  rows.append(dict(attempt=d.parent.name,harness=m[1],result=result,failed_checks=failed,unwind_failure=any('unwind' in c.lower() for c in failed)))
(E/'KMX_RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
print('verified harness records',len(rows))
for r in rows:
 print(r['attempt'],r['harness'],r['result'],'UNWIND' if r['unwind_failure'] else '')
