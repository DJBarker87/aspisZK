"""Expose opaque declarations and thread their parameters through emitted calls.
Only signatures/call syntax change; raw emission is retained unmodified.
"""
from pathlib import Path
import re,json,difflib
E=Path(__file__).resolve().parent;R=E/'NJS_emitted/raw/NJS_Extract';D=E/'NJS_Extract';D.mkdir(exist_ok=True)
types=(R/'Types.lean').read_text();adapt=re.sub(r'\bdiscriminant isize,?\s*','',types);adapt=re.sub(r'@\[\]\s*\n','',adapt);(D/'Types.lean').write_text(adapt)
extern=(R/'FunsExternal_Template.lean').read_text();decls=re.findall(r'^axiom\s+(\S+)\s*([\s\S]*?)(?=\n/--|\Z)',extern,re.M);vs=[];maps=[]
for i,(name,sig) in enumerate(decls):
 sig=sig.strip();depth=0
 for j,ch in enumerate(sig):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:break
 bind=sig[:j].strip();ty=sig[j+1:].strip();var='NJS_call_'+str(i);vs.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')');maps.append(dict(generated_name=name,parameter=var,signature=sig))
s=(R/'Funs.lean').read_text().replace('import NJS_Extract.FunsExternal\n','');needle='namespace NJS_Extract\n';s=s.replace(needle,needle+'\n'+'\n\n'.join(vs)+'\n',1)
for m in sorted(maps,key=lambda x:-len(x['generated_name'])):s=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'])+r'(?![A-Za-z0-9_.])',m['parameter'],s)
# Discover declaration blocks, compute section-parameter closure, then apply at each reference.
heads=list(re.finditer(r'^def\s+([\w.]+)',s,re.M));blocks={};regions={}
for k,h in enumerate(heads):
 end=heads[k+1].start() if k+1<len(heads) else len(s);chunk=s[h.start():end];assign=chunk.index(':=')+2;name=h[1];blocks[name]=chunk[assign:];regions[name]=(h.start()+assign,end)
rx=lambda n:r'(?<![\w.])'+re.escape(n)+r'(?![\w.])'
params={n:set(re.findall(r'NJS_call_\d+',b)) for n,b in blocks.items()}
for _ in range(len(blocks)):
 old={n:set(v) for n,v in params.items()}
 for n,b in blocks.items():
  for child in blocks:
   if child!=n and re.search(rx(child),b):params[n].update(old[child])
 if params==old:break
out=s
for n,(start,end) in sorted(regions.items(),key=lambda x:-x[1][0]):
 b=s[start:end]
 for child in sorted(blocks,key=lambda x:-len(x)):
  if child!=n and params[child]:b=re.sub(rx(child),'('+child+' '+' '.join(sorted(params[child],key=lambda x:int(x.rsplit('_',1)[1])))+')',b)
 out=out[:start]+b+out[end:]
# Charon's integer shift literal inferred as I32; pinned Aeneas wrapping shift takes U32.
assert out.count('8#i32')==2
out=out.replace('8#i32','8#u32')
(D/'Funs.lean').write_text(out);(E/'NJS_PARAMETERS.json').write_text(json.dumps(dict(externals=maps,threading={n:sorted(v) for n,v in params.items() if v}),indent=2)+'\n')
for stem,before,after in [('Types',types,adapt),('Funs',(R/'Funs.lean').read_text(),out)]: (E/('NJS_'+stem+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem+'.lean',tofile='NJS_Extract/'+stem+'.lean')))
print('parameterized external declarations; threaded exact section arguments')
