#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2]
p=R/'crates/aspis-r1-cost-probe/src/verifier.rs';s=p.read_text()
def function(name):
 a=s.index('fn '+name+'(');b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
a=s.index("struct Reader<'a>");b=s.index('\n\n\n#[inline(always)]\nfn validate_checkpoint_queries',a)
reader=s[a:b].rstrip()
sections='\n\n'.join(function(n) for n in ['read_checkpoint_weights','read_checkpoint_semantic_alpha'])
for name,text in [('reader-source.rs',reader+'\n'),('sections-source.rs',sections+'\n')]:
 q=R/'tools/ckpt-bytes3-20261022/src'/name
 if '--write' in sys.argv:q.write_text(text)
 assert q.read_text()==text,name
print(json.dumps({'source':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'reader_exact':True,'sections_exact':True}))
