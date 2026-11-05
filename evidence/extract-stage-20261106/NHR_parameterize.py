"""Expose generated opaque callees as parameters; preserve raw files separately.
This is a syntax-only compilation interface, not a callee semantics/refinement proof.
"""
from pathlib import Path
import argparse,json,re,hashlib,difflib
E=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('function');p.add_argument('--raw',required=True);a=p.parse_args()
raw=E/a.raw;dest=E/'NHR_lean'/('NHR_'+a.function);dest.mkdir(parents=True,exist_ok=True)
types=(raw/'Types.lean').read_text()
# The global discriminant macro names ignore the namespace. Do not register duplicate metadata.
adapted=re.sub(r'\bdiscriminant isize,?\s*','',types)
(dest/'Types.lean').write_text(adapted)
extern=(raw/'FunsExternal_Template.lean').read_text()
# A declaration extends to the next documentation block or end of file.
decls=re.findall(r'^axiom\s+(\S+)\s*([\s\S]*?)(?=\n/--|\Z)',extern,re.M)
assert decls
variables=[];mapping=[]
for i,(name,sig) in enumerate(decls):
 sig=sig.strip();depth=0;colon=None
 for j,ch in enumerate(sig):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:colon=j;break
 assert colon is not None,(name,sig)
 bind=sig[:colon].strip();ty=sig[colon+1:].strip();var='NHR_call_'+str(i)
 variables.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')')
 mapping.append(dict(generated_name=name,parameter=var,signature=sig))
funs=(raw/'Funs.lean').read_text().replace('import NHR_'+a.function+'.FunsExternal\n','')
# Add variables inside the generated namespace, where generated types resolve.
needle='namespace NHR_'+a.function+'\n';assert needle in funs
funs=funs.replace(needle,needle+'\n-- Opaque callees are explicit parameters, never axioms.\n'+'\n\n'.join(variables)+'\n',1)
for m in sorted(mapping,key=lambda x:-len(x['generated_name'])):
 funs=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'])+r'(?![A-Za-z0-9_.])',m['parameter'],funs)
funs+='\n#print axioms NHR_'+a.function+'.verifier.candidate.'+a.function+'\n'
(dest/'Funs.lean').write_text(funs)
for stem,before,after in [('Types',types,adapted),('Funs',(raw/'Funs.lean').read_text(),funs)]:
 (dest/(stem+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem+'.lean',tofile='compile/'+stem+'.lean')))
(dest/'NHR_PARAMETERS.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(dest)
