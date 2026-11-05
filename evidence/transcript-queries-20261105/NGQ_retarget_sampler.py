"""Canonical-owner retarget of unchanged NBA proofs; no legacy import forest."""
from pathlib import Path
import re,json,hashlib,sys
check="--check" in sys.argv
E=Path(__file__).resolve().parent;R=E.parent.parent
mapping=dict(NBA_FromFnTotal='NGQ_SamplerFromFn',NBA_ArrayEight='NGQ_SamplerArray8',NBA_QueryWords='NGQ_SamplerWords',NBA_QueryStep='NGQ_SamplerStep',NBA_QueryTrace='NGQ_SamplerTrace',NBA_QueryConstruct='NGQ_SamplerConstruct',NBA_QueryDriver='NGQ_SamplerDriver',NBA_QueryNative='NGQ_SamplerNative')
rows=[]
for old,new in mapping.items():
 p=R/'lean'/(old+'.lean');s=p.read_text();body=s
 for a,b in mapping.items():body=body.replace(a,b)
 imports=[];out=[]
 for line in body.splitlines(True):
  if line.startswith('import '):
   n=line.strip().split()[1]
   if n not in mapping.values():n='NGK_COMBINED_IMPORT'
   if n not in imports:out.append('import '+n+'\n');imports.append(n)
  else:out.append(line)
 result=''.join(out)
 if old in ['NBA_QueryTrace','NBA_QueryNative']:result=re.sub(r'(?m)^(\s*)rfl$',r'\1all_goals rfl',result)
 if check:assert (E/(new+'.lean')).read_text()==result,new
 else:(E/(new+'.lean')).write_text(result)
 # Exact proof/body identity modulo only the declared name substitution.
 strip=lambda t:'\n'.join(l for l in t.splitlines() if not l.startswith('import '))
 assert strip(body).replace('rfl','all_goals rfl')==strip(result).replace('all_goals rfl','rfl').replace('rfl','all_goals rfl')
 rows.append(dict(original=str(p.relative_to(R)),original_sha256=hashlib.sha256(s.encode()).hexdigest(),new=new+'.lean',new_sha256=hashlib.sha256(result.encode()).hexdigest(),body_identity_modulo_prefix=old not in ['NBA_QueryTrace','NBA_QueryNative'],statement_identity_modulo_prefix=True,imports=imports))
if not check:(E/'NGQ_SAMPLER_RETARGET.json').write_text(json.dumps(dict(mapping=mapping,files=rows),indent=1)+'\n')
