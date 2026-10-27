"""Reuse byte-identical extracted helper definitions; never invent an external leaf."""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2];directory=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';ev=root/'evidence/pv-cblib-20261027'
namespace,rawpath=sys.argv[1:3];raw=Path(rawpath).read_text()
def definitions(s):
 matches=list(re.finditer(r'^def ([\w.]+)\b',s,re.M));result={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else s.index('\nend ',m.end())
  body=s[m.start():end];body=body.split('/--')[0].split('#print axioms')[0].rstrip()
  result[m[1]]=body
 return result
def norm(s):
 s=re.sub(r'/\*.*?\*/','',s,flags=re.S)
 s=re.sub(r'--[^\n]*','',s)
 return re.sub(r'\s+','',s)
known={}
for name in ['PV_CBL_FallbackBlock','PV_CBL_ShaBytes','PV_CBL_ShaPadFixed','PV_CBL_FinalSoft']:
 if not (directory/f'{name}.lean').exists(): continue
 for k,v in definitions((directory/f'{name}.lean').read_text()).items():known[k]=(name,v)
matched={};remaining={}
for k,v in definitions(raw).items():
 if k in known:
  owner,old=known[k]
  assert norm(v)==norm(old),(k,'different extracted definition; do not reuse')
  matched[k]=owner
 else:remaining[k]=v
imports=sorted(set(matched.values()))
s='import Aeneas\n'+'\n'.join('import R1Z.'+x for x in imports)+'\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace '+namespace+'\n'
# Replacements longest-first to avoid prefix substitution of helper names.
for k,v in remaining.items():
 for word in sorted(matched,key=len,reverse=True):
  v=re.sub(r'(?<![\w.])'+re.escape(word)+r'(?![\w.])',matched[word]+'.'+word,v)
 s+=v+'\n\n'
s+='\n'.join('#print axioms '+k for k in remaining)+'\nend '+namespace+'\n'
(directory/f'{namespace}.lean').write_text(s)
r=dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),result_sha256=hashlib.sha256(s.encode()).hexdigest(),reused=matched,remaining=list(remaining),method='whitespace/comment-normalized exact generated definition equality; helper namespaces rebound to existing identical definitions; no external template',source_file=rawpath)
(ev/(namespace+'-port.json')).write_text(json.dumps(r,indent=2)+'\n')
print(namespace,len(matched),'identical helpers;',len(remaining),'new definitions')
