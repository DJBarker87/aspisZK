from pathlib import Path
import re,json,difflib
E=Path(__file__).parent;raw=E/'NJA_emitted/raw/NHR_NJA_multiproof';out=E/'NJA_lean/NJA_Multiproof';out.mkdir(parents=True,exist_ok=True)
orig=(raw/'Types.lean').read_text();types=orig.replace('NHR_NJA_multiproof','NJA_Multiproof').replace('import NJA_Multiproof.TypesExternal\n','');types=re.sub(r'@\[discriminant isize\]\n','',types);(out/'Types.lean').write_text(types)
extern=(raw/'FunsExternal_Template.lean').read_text();decls=re.findall(r'^axiom\s+(\S+)\s*([\s\S]*?)(?=\n/--|\Z)',extern,re.M);variables=['variable (NJA_Windows : Type → Type)'];mapping=[]
for i,(name,sig) in enumerate(decls):
 sig=sig.strip().replace('core.slice.iter.Windows','NJA_Windows');depth=0
 for j,ch in enumerate(sig):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:break
 assert ch==':'
 bind=sig[:j].strip();ty=sig[j+1:].strip();var='NJA_call_'+str(i)
 variables.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')');mapping.append(dict(generated_name=name,parameter=var,signature=sig))
origf=(raw/'Funs.lean').read_text();funs=origf.replace('NHR_NJA_multiproof','NJA_Multiproof').replace('import NJA_Multiproof.FunsExternal\n','');funs=funs.replace('namespace NJA_Multiproof\n','namespace NJA_Multiproof\n\n-- Exact external signatures are explicit parameters; no callee laws assumed.\n'+'\n\n'.join(variables)+'\n',1);funs=funs.replace('core.slice.iter.Windows','NJA_Windows')
for m in sorted(mapping,key=lambda x:-len(x['generated_name'])):funs=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'].replace('core.slice.iter.Windows','NJA_Windows'))+r'(?![A-Za-z0-9_.])',m['parameter'],funs)
funs+='\n#print axioms NJA_Multiproof.multiproof.verify_in_place\n';(out/'Funs.lean').write_text(funs)
for stem,before,after in [('Types',orig,types),('Funs',origf,funs)]:
 (E/('NJA_'+stem+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem,tofile='parameterized/'+stem)))
(E/'NJA_PARAMETERS.json').write_text(json.dumps(mapping,indent=2)+'\n');print('NJA parameterization: exact opaque signatures, Windows type family explicit; no axioms compiled')
