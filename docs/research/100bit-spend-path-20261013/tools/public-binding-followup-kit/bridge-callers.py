#!/usr/bin/env python3
"""Same five naming expansions on current callers, with full old-decl inventory."""
from pathlib import Path
import argparse,hashlib,importlib.util,inspect,json,re
ROOT=Path(__file__).resolve().parents[5]
B=ROOT/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
# Keep strings atomic while discarding whitespace; changes inside strings count.
def uncomment(text):
 out=[];i=0;depth=0
 while i<len(text):
  if text[i:i+2]=='/-':depth+=1;i+=2
  elif depth and text[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif text[i:i+2]=='--':
   at=text.find('\n',i);i=len(text) if at<0 else at
  elif text[i]=='"':
   start=i;i+=1
   while i<len(text):
    if text[i]=='\\':i+=2
    elif text[i]=='"':i+=1;break
    else:i+=1
   out.append(text[start:i])
  else:out.append(text[i]);i+=1
 return ''.join(out)
def tokens(text):return re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+',uncomment(text))
def declarations(raw):
 text=uncomment(raw.decode());pat=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:def|structure|inductive|abbrev|instance)\s+(\S+)',re.M)
 matches=list(pat.finditer(text));result={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else text.rfind('\nend ')
  body=text[m.start():end];name=m[1]
  # Attributes belong to the following declaration, so exclude trailing attrs.
  body=re.sub(r'\s*@\[[^\]]*\]\s*$','',body)
  assert name not in result,name
  result[name]=tokens(body)
 return result
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--generated',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 spec=importlib.util.spec_from_file_location('original',B/'tools/public-preparation-discriminant-bridge.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 raw=(a.generated/'Types.lean').read_bytes();m.expected=sha(raw)
 code=inspect.getsource(m.adapt);assert code.count(" and s.count('@[discriminant isize]')==0")==1
 code=code.replace(" and s.count('@[discriminant isize]')==0",'')
 exec(code,m.__dict__);adapted,instances=m.adapt(raw)
 out=a.out/'AspisR1PublicPreparation';out.mkdir(parents=True,exist_ok=True)
 (out/'Types.lean').write_bytes(adapted);(out/'Funs.lean').write_bytes((a.generated/'Funs.lean').read_bytes())
 inventory={}
 for file in ['Types.lean','Funs.lean']:
  old=(B/'lean/extracted-public-preparation-20261016/AspisR1PublicPreparation'/file).read_bytes();new=(a.generated/file).read_bytes()
  prior=declarations(old);now=declarations(new);entries=[]
  for name,tok in prior.items():
   assert name in now,(file,name)
   assert tok==now[name],(file,name,'actual declaration tokens changed')
   h=sha(json.dumps(tok,separators=(',',':')).encode());entries.append({'declaration':name,'classification':'unchanged','token_sha256':h})
  inventory[file]={'old_sha256':sha(old),'current_raw_sha256':sha(new),'unchanged_declarations':entries,'new_declarations':sorted(set(now)-set(prior))}
 record={'raw_types_sha256':sha(raw),'adapted_types_sha256':sha(adapted),'adapted_funs_sha256':sha((out/'Funs.lean').read_bytes()),'rule':'Original five constructor readers expanded with qualified instance names only; inverse exact by existing adapter. Every original declaration token stream equal; comments/whitespace/order excluded. No function or carrier substitutions.','instances':instances,'declarations':inventory}
 (a.out/'adapter-pins.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'old_declarations_unchanged':sum(len(x['unchanged_declarations']) for x in inventory.values()),'adapted_types_sha256':sha(adapted)}))
if __name__=='__main__':main()
