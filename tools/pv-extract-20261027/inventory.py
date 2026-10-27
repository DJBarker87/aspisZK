from pathlib import Path
import subprocess,json,re
E=Path('evidence/pv-extract-20261027'); hits=(E/'inventory-grep.txt').read_text().splitlines(); records=[]; seen=set()
for h in hits:
 if 'escaping reference output requires loan validation' not in h or '/output.log:' not in h:continue
 ref,path=h.split(':',2)[:2]; folder=path.rsplit('/',1)[0]
 if folder in seen:continue
 seen.add(folder)
 for n in ['target.json','collected-receipt.json']:
  p=subprocess.run(['git','show',ref+':'+folder+'/'+n],capture_output=True,text=True)
  if p.returncode==0:
   r=json.loads(p.stdout)
   if 'target' in r:break
 else:continue
 target=r['target']; records.append(dict(ref=ref,revision=subprocess.check_output(['git','rev-parse',ref],text=True).strip(),evidence=folder,target=target,llbc=target[-1]))
(E/'inventory-inputs.json').write_text(json.dumps(records,indent=2)+'\n'); print(len(records))
