#!/usr/bin/env python3
"""Index extraction pin receipts without inferring tool identity from a name."""
import json,pathlib,re,collections
from NKT_checker import Git,sha
P=pathlib.Path(__file__).parent

def main():
 a=json.load(open(P/'NKT_AUDIT.json'));g=Git(a['audit_revision']);metas=[]
 for p in g.entries:
  if not p.endswith('.json') or '/sources/' in p:continue
  if not re.search(r'(?:PINS|EXTRACTION|EXTRACT|ENV|TOOL|INPUT)',pathlib.PurePosixPath(p).name):continue
  if p.count('/')>6:continue
  b=g.read(p)
  if len(b)>3000000:continue
  s=b.decode(errors='replace')
  # Actual pin values are retained as strings with surrounding keys, not guessed.
  ts=[]
  for m in re.finditer(r'[0-9a-f]{64}',s):
   context=s[max(0,m.start()-200):min(len(s),m.end()+70)]
   if re.search(r'charon|aeneas',context,re.I):ts.append({'sha256':m.group(),'context':context})
  if ts:metas.append({'path':p,'sha256':sha(b),'tool_pin_contexts':ts,'text':s})
 records=[]
 for h,aliases in a['emission_aliases'].items():
  # Only aliases present in the main audit are relevant to this artifact.
  own=[f for f in a['functions'] if f['emission_sha256']==h]
  if not own:continue
  direct=[m for m in metas if h in m['text']]
  dirs={str(pathlib.PurePosixPath(p).parents[len(pathlib.PurePosixPath(p).parts)-3]) for p in aliases if p.startswith('evidence/')}
  nearby=[m for m in metas if any(m['path'].startswith(d+'/') for d in dirs)]
  chosen=direct if direct else nearby
  records.append({'extraction_id':h,'emission_paths':aliases,'emitted_file_sha256':h,'origin_status':'HASH_LINKED_PIN_RECEIPT' if direct else ('SAME_PACKET_METADATA_ONLY' if nearby else 'UNRESOLVED_TOOL_ORIGIN'),
   'pin_receipts':[{k:v for k,v in m.items() if k!='text'} for m in chosen]})
 P.joinpath('NKT_EXTRACTIONS.json').write_text(json.dumps(records,indent=1)+'\n')
 print(json.dumps({'emission_blobs':len(records),'hash_linked':sum(x['origin_status']=='HASH_LINKED_PIN_RECEIPT' for x in records),'same_packet_only':sum(x['origin_status']=='SAME_PACKET_METADATA_ONLY' for x in records),'unresolved':sum(x['origin_status']=='UNRESOLVED_TOOL_ORIGIN' for x in records)}))
if __name__=='__main__':main()
