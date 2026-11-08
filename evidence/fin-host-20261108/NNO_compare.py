"""Compare complete source declaration headers after explicit namespace transport."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent
names=['NoWritePool','NoWriteOwned','NoWrite241','G2Reference','TasRoots','CandidateRoots','NNCWeak','Carrier','Dispatch','DispatchEmitted','Reify','Folds','TAS']
changed={n:'NVR_'+n for n in ['NoWritePool','NoWriteOwned','NoWrite241','G2Reference','TasRoots','CandidateRoots','NNCWeak']}
def clean(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);return re.sub(r'--[^\n]*','',s)
def headers(s):
 s=clean(s);out={}
 for m in re.finditer(r'(?m)^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',s):
  end=s.find(':=',m.end());out[m[1]]=re.sub(r'\s+',' ',s[m.start():end]).strip()
 return out
rows=[]
for n in names:
 new=R/'nvr-20261108'/('NVR_'+n+'.lean')
 old=R/('stage-wrap-20261111'if n in changed else'entry-rsl-20261111')/(('NMV_'if n in changed else'NNF_')+('Dispatch'if n=='DispatchEmitted'else n)+'.lean')
 a=old.read_text();b=new.read_text();h=headers(a);k=headers(b)
 for suffix,replacement in changed.items():a=a.replace('NMV_'+suffix,replacement)
 a=a.replace('NNF_','NVR_');h=headers(a)
 comparisons=[]
 for key,v in k.items():
  if key not in h:
   comparisons.append(dict(name=key,status='ADDED'if n=='NoWritePool'and key in ['ofCloned_free','data_free','verifierCheckpoint_free']else'UNMATCHED',new_header=v));continue
  comparisons.append(dict(name=key,status='SAME'if h[key]==v else'DIFFERENT',old_header=h[key],new_header=v))
 rows.append(dict(module=new.stem,old_source=str(old),old_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),new_sha256=hashlib.sha256(new.read_bytes()).hexdigest(),comparisons=comparisons))
report=dict(method='Complete source declaration headers including all explicit binders; comments/whitespace removed, only named namespace transport. Kernel checks and standard-axiom audits are separate. New combined module has no old analogue.',rows=rows)
(E/'NNO_STATEMENT_COMPARISON.json').write_text(json.dumps(report,indent=1)+'\n')
print([(z['module'],[(c['name'],c['status'])for c in z['comparisons']if c['status']!='SAME'])for z in rows])
