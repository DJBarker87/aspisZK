"""Expose generated opaque callees as parameters; preserve raw files separately.
This is a syntax-only compilation interface, not a callee semantics/refinement proof.
"""
from pathlib import Path
import argparse,json,re,hashlib,difflib
E=Path(__file__).resolve().parent
raw=E/'NJI_EMITTED/raw/NJI_Extracted';dest=E
types=(raw/'Types.lean').read_text()
# The global discriminant macro names ignore the namespace. Do not register duplicate metadata.
adapted=re.sub(r'\bdiscriminant isize,?\s*','',types)
adapted=re.sub(r'@\[\]\s*\n','',adapted)
(dest/'NJI_Extracted.Types.lean').write_text(adapted)
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
 bind=sig[:colon].strip();ty=sig[colon+1:].strip();var='NJI_call_'+str(i)
 variables.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')')
 mapping.append(dict(generated_name=name,parameter=var,signature=sig))
funs=(raw/'Funs.lean').read_text().replace('import NJI_Extracted.FunsExternal\n','')
# Add variables inside the generated namespace, where generated types resolve.
needle='namespace NJI_Extracted\n';assert needle in funs
funs=funs.replace(needle,needle+'\n-- Opaque callees are explicit parameters, never axioms.\n'+'\n\n'.join(variables)+'\n',1)
for m in sorted(mapping,key=lambda x:-len(x['generated_name'])):
 funs=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'])+r'(?![A-Za-z0-9_.])',m['parameter'],funs)
roots=['aspis_statement.pool_v1.format.decode_verifier_policy_v1','aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_checkpoint_v1','aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_master_v1','aspis_statement.pool_v1.pair_forest_accounts.validate_master','aspis_statement.pool_v1.verifier_registry.decode_verifier_registry_entry_v1','aspis_statement.pool_v1.verifier_registry.decode_verifier_registry_v1','aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1','aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1']
funs+='\n'+''.join('#print axioms NJI_Extracted.'+r+'\n' for r in roots)
(dest/'NJI_Extracted.Funs.lean').write_text(funs)
for stem,before,after in [('Types',types,adapted),('Funs',(raw/'Funs.lean').read_text(),funs)]:
 (dest/('NJI_'+stem+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem+'.lean',tofile='compile/'+stem+'.lean')))
(dest/'NJI_PARAMETERS.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(dest)

# Isolate the available declarations; rejected/omitted roots stay in raw and failed Funs.
blocks=re.split(r'(?=/--)',funs)
kept=[];removed=[]
for b in blocks:
 if ('impl_def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT' in b or
     re.search(r'\bdef\s+aspis_statement\.pool_v1\.pair_forest_accounts\.validate_master(?:[.\s])',b)):
  removed.append(b)
 else:kept.append(b)
core=''.join(kept)
core=re.sub(r'^#print axioms.*\n','',core,flags=re.M)
core+='\n'+''.join('#print axioms NJI_Extracted.'+r+'\n' for r in [roots[0],roots[6],roots[7]])
(dest/'NJI_Extracted.Core.lean').write_text(core)
(dest/'NJI_CORE_SPLIT.json').write_text(json.dumps(dict(removed_blocks=len(removed),reason='Unused incompatible IterMut trait and capacity-parameter-dependent master SCC excluded; no changed function body',retained_roots=[roots[0],roots[6],roots[7]]),indent=2))
(dest/'NJI_Core.diff').write_text(''.join(difflib.unified_diff(funs.splitlines(True),core.splitlines(True),fromfile='failed/Funs.lean',tofile='isolated/Core.lean')))
