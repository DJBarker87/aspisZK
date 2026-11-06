"""Package retained native receipts for validation only; no native execution."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'pc-helpers1-20261110'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
closed=read(P/'PCB_CLOSED.json');cand=read(P/'PCB_CANDIDATES.json');rows=closed+cand
pairs=[]
for r in closed:
 if r.get('native'):pairs.append([r['native'],r['negative']])
 if r.get('native_correct_place'):pairs.append([r['native_correct_place'],r['native_wrong_place']])
pairs += [['PCB_K111','PCB_K112'],['PCB_K113','PCB_K114'],['PCB_K070','PCB_K071'],['PCB_K072','PCB_K078'],['PCB_K115','PCB_K116'],['PCB_K117','PCB_K118']]
ids=sorted(set(a for p in pairs for a in p)|{'PCB_K074','PCB_K075','PCB_K076','PCB_K077','PCB_K119'})
records={}
for a in ids:
 def path(s):
  q=P/(a+s)
  return q if q.exists() else E/'PCE_PREDECESSOR_NATIVE'/(a+s)
 record=dict(config=read(P/(a+'.json')),receipt=read(P/a/'receipt.json'),stdout=(P/a/'stdout.log').read_text())
 for k,s in [('graph','-graph-check.json'),('lock','-lock-check.json')]:record[k]=read(path(s))
 record['features']=path('-selected-features.txt').read_text()
 record['input_pins']={str(p):sha(p) for p in [P/(a+'.json'),P/a/'receipt.json',P/a/'stdout.log',path('-graph-check.json'),path('-lock-check.json'),path('-selected-features.txt')]}
 records[a]=record
x=dict(pairs=pairs,records=records,packet_rows=rows,classification='REVALIDATION of retained evidence; no native run; accepted re-gates inherited certificates remain retained')
(E/'PCE_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
print('Packaged '+str(len(records))+' retained native verdict/graph/lock/feature receipts for read-only validation.')
