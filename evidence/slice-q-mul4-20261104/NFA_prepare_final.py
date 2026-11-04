from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;entries=[]
for p in sorted(E.glob('NFA_*.lean')):
 if not re.search(r'^theorem ',p.read_text(),re.M):continue
 name=p.stem;h=hashlib.sha256(p.read_bytes()).hexdigest();good=[]
 for rc in E.glob('NFA_L*/receipt.json'):
  x=json.loads(rc.read_text())
  if x['kind']=='lean' and x['module']==name and x['exit_status']==0 and x['source_hashes'].get('NFA_generated/'+name+'.lean')==h:good.append((rc,x))
 assert len(good)==1,(name,len(good))
 rc,x=good[0];roots=[]
 for line in x['print_axioms']:
  m=re.match("'([^']+)'",line);assert m and 'NFA_' in m[1] and 'sorryAx' not in line
  roots.append(m[1])
 assert len(roots)==len(re.findall(r'^theorem ',p.read_text(),re.M)),name
 entries.append(dict(module=name,source_sha256=h,source_attempt=x['attempt'],roots=roots))
s='\n'.join('import '+x['module'] for x in entries)+'\n\n'+'\n'.join('#print axioms '+root for x in entries for root in x['roots'])+'\n'
(E/'NFA_FinalAudit.lean').write_text(s)
(E/'NFA_FINAL_MANIFEST.json').write_text(json.dumps(dict(status='PREPARED',entries=entries,standard_axioms=['propext','Classical.choice','Quot.sound'],final_target='NFA_FinalAudit',final_attempt='NFA_L100',scope='One coherent NFA math forest on pinned SInt2/Aeneas objects; not a full frozen release replay'),indent=2)+'\n')
print(len(entries),'modules',sum(len(x['roots']) for x in entries),'theorems')
