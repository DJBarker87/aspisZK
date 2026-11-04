#!/usr/bin/env python3
"""Index historical extraction/native/Kani receipts outside pv-* without transferring credit."""
import collections,hashlib,json,re,subprocess
from pathlib import Path
import PV_MF_check as C
D=Path(__file__).resolve().parent;B='85addf5a9764aa5e17d28bd6cf96bbda084447c5'
mods=C.load('MODULES.json');bybase=collections.defaultdict(list)
for p in mods:bybase[Path(p).stem].append(p)
tr={}
for l in subprocess.check_output(['git','ls-tree','-rl',B],text=True).splitlines():
 mt,p=l.split('\t',1);a=mt.split();
 if a[1]=='blob':tr[p]=(a[2],int(a[3]))
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(h):
 proc.stdin.write((h+'\n').encode());proc.stdin.flush();a=proc.stdout.readline().split();b=proc.stdout.read(int(a[2]));proc.stdout.read(1);return b
out={};count=0
for p,(h,n) in tr.items():
 if not (p.endswith('.json') and '/evidence/' in p and n<5_000_000 and any(t in p.lower() for t in ['source','receipt','manifest','assoc','pins'])):continue
 b=blob(h);s=b.decode(errors='replace');matches=set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*',s))&bybase.keys()
 matches={n for n in matches if len(n)>8 or n.startswith('PV_')}
 if not matches:continue
 out[p]={'git_blob':h,'sha256':hashlib.sha256(b).hexdigest(),'module_basenames':sorted(matches),'scope':'historical receipt/module discovery only; source association NOT transferred'};count+=1
parts=[];items=list(out.items())
for k in range(0,len(items),20):
 name=f'SUPPLEMENT-part{k//20:03}.json';b=(json.dumps(dict(items[k:k+20]),indent=1)+'\n').encode();assert len(b)<20_000_000;(D/name).write_bytes(b);parts.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
(D/'SUPPLEMENT.json').write_text(json.dumps({'sharded':parts,'kind':'dict'},indent=1)+'\n');print('supplemental receipts',count)
