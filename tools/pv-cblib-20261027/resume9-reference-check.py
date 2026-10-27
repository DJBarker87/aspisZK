"""Check exact owned codec/reference bodies used by the loop-free P6 links."""
from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parents[2]
a=(root/'tools/pv-cblib-20261027/lib.rs').read_text()
b=(root/'tools/pv-cblib-20261027/kani-lib.rs').read_text().split('mod resume9_links {',1)[1]
def body(s,name):
 start=re.search(r'fn '+name+r'(?:<[^>]+>)?\(',s).start();op=s.index('{',start);d=1;i=op+1
 while d:
  d+=(s[i]=='{')-(s[i]=='}');i+=1
 return re.sub(r'\s+','',s[op:i])
r={}
for x,y in [('sha_load_be4','load'),('sha_store_be4','store'),('pop_copy_resize_reference','pop_resize'),('join_resize_reference','join_resize')]:
 c=body(a,x);d=body(b,y);assert c==d,(x,c,d)
 r[x]={'kani_function':y,'body_sha256':hashlib.sha256(c.encode()).hexdigest()}
(root/'evidence/pv-cblib-20261027/resume9-reference-bodies.json').write_text(json.dumps({'status':'PASS','references':r},indent=2)+'\n')
print('PASS')
