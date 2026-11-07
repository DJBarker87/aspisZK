"""Expose generated opaque callees as parameters; preserve raw files separately.
This is a syntax-only compilation interface, not a callee semantics/refinement proof.
"""
from pathlib import Path
import argparse,json,re,hashlib,difflib
E=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('function');p.add_argument('--raw',required=True);a=p.parse_args()
raw=E/a.raw;dest=E/'NMT_lean'/('NMT_'+a.function);dest.mkdir(parents=True,exist_ok=True)
types=(raw/'Types.lean').read_text()
# The global discriminant macro names ignore the namespace. Do not register duplicate metadata.
adapted=re.sub(r'\bdiscriminant isize,?\s*','',types)
adapted=re.sub(r'@\[\]\s*\n','',adapted)
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
 bind=sig[:colon].strip();ty=sig[colon+1:].strip();var='NMT_call_'+str(i)
 variables.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')')
 mapping.append(dict(generated_name=name,parameter=var,signature=sig))
funs=(raw/'Funs.lean').read_text().replace('import NMT_'+a.function+'.FunsExternal\n','')
# Add variables inside the generated namespace, where generated types resolve.
needle='namespace NMT_'+a.function+'\n';assert needle in funs
funs=funs.replace(needle,needle+'\n-- Opaque callees are explicit parameters, never axioms.\n'+'\n\n'.join(variables)+'\n',1)
for m in sorted(mapping,key=lambda x:-len(x['generated_name'])):
 funs=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'])+r'(?![A-Za-z0-9_.])',m['parameter'],funs)
# Make generalized local dependencies explicit at every subsequent definition.
# Lean does not infer section parameters from a bare trait-method constant.
params=[m['parameter'] for m in mapping]
pattern=r'\bdef\s+(\S+)'
starts=list(re.finditer(pattern,funs)); rebuilt=funs[:starts[0].start()];known=[]
for j,d in enumerate(starts):
 end=starts[j+1].start() if j+1<len(starts) else len(funs)
 chunk=funs[d.start():end];name=d[1];offset=len(d[0])
 head,body=chunk[:offset],chunk[offset:]
 for earlier,uses in sorted(known,key=lambda z:-len(z[0])):
  if not uses:continue
  body=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(earlier)+r'(?![A-Za-z0-9_.])',lambda _: '('+earlier+' '+' '.join(uses)+')',body)
 uses=[v for v in params if re.search(r'(?<![A-Za-z0-9_])'+v+r'(?![A-Za-z0-9_])',body)]
 known.append((name,uses));rebuilt+=head+body
funs=rebuilt
root={'tx1':'verifier.candidate.tx1','first':'first_decoded','stage1_owned':'r1_pool_adapter.owned.stage1_owned'}[a.function]
funs+='\n#print axioms NMT_'+a.function+'.'+root+'\n'
(dest/'Funs.lean').write_text(funs)
for stem,before,after in [('Types',types,adapted),('Funs',(raw/'Funs.lean').read_text(),funs)]:
 (dest/(stem+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem+'.lean',tofile='compile/'+stem+'.lean')))
(dest/'NMT_PARAMETERS.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(dest)
