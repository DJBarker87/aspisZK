"""Read retained raw CBMC JSON without rerunning any gate."""
from pathlib import Path
import json,sys,lzma,hashlib
E=Path(__file__).resolve().parent
def documents(s):
 dec=json.JSONDecoder();i=0
 while i<len(s):
  j=s.find('[',i)
  if j<0:return
  try:v,k=dec.raw_decode(s[j:])
  except ValueError:i=j+1;continue
  if isinstance(v,list) and v and isinstance(v[0],dict) and any('program' in x or 'result' in x or 'cProverStatus' in x for x in v if isinstance(x,dict)):yield v
  i=j+k
for n in sys.argv[1:]:
 D=E/'host'/n;p=D/'output.log';s=p.read_text() if p.exists() else lzma.decompress((D/'output.log.xz').read_bytes()).decode();out=[]
 docs=list(documents(s))
 for p in sorted(D.glob('cbmc-*.json')):
  if p.name.endswith('-command.json'):continue
  try:v=json.loads(p.read_text())
  except ValueError:continue
  if isinstance(v,list):docs.append(v)
 for doc in docs:
  props=[p for x in doc for p in x.get('result',[])]
  failed=[p for p in props if p.get('status')=='FAILURE']
  out.append({'statuses':[x['cProverStatus'] for x in doc if 'cProverStatus'in x],'checks':len(props),'failed':failed})
 (D/'trace-summary.json').write_text(json.dumps(out,indent=2)+'\n')
 print(n,[(x['statuses'],x['checks'],[(f.get('property'),f.get('description'),len(f.get('trace',[]))) for f in x['failed']]) for x in out])
