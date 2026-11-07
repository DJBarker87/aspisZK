from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;src=E/'PCD_request_extracted/PCD_FrozenRequest'
types=(src/'Types.lean').read_text()
names=[m.group(1).split('.')[-1] for m in re.finditer(r'@\[discriminant isize,.*?\]\s*inductive (\S+)',types,re.S)]
assert len(names)==9,(len(names),names)
mapping={n:'PCD_'+n for n in names}
def retarget(text,inverse=False):
 table={v:k for k,v in mapping.items()} if inverse else mapping
 regex=re.compile(r'\b('+'|'.join(map(re.escape,table))+r')\b')
 parts=re.split(r'("(?:[^"\\]|\\.)*")',text)
 return ''.join(part if i%2 else regex.sub(lambda m:table[m[0]],part) for i,part in enumerate(parts))
manifest={}
for f in ['Types','Funs']:
 raw=(src/(f+'.lean')).read_text();out=retarget(raw);assert retarget(out,True)==raw
 (E/('PCD_FrozenRequest.'+f+'.lean')).write_text(out)
 manifest[f]={'original_sha256':hashlib.sha256(raw.encode()).hexdigest(),'compiled_sha256':hashlib.sha256(out.encode()).hexdigest(),'reversible':True}
(E/'PCD_REQUEST_NAME_FIX.json').write_text(json.dumps({'finding':'Aeneas discriminant attributes generate global short names that collide with retained emitted types','reason':'L040 import rejected before checking any theorem','kind':'new generated type identifiers only; constructor/field bodies and quoted Rust origin names preserved','renames':mapping,'files':manifest,'no_kani_harness_rename':True},indent=1)+'\n')
print('Applied reversible prefix fix to nine generated type identifiers; no datatype or Rust-origin change.')
