"""Pin deployed218 per-link and post220 tail windows against frozen source."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_SumCopy_native.rs.txt').read_text()
def braces(s,p):
 p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
parent=braces(old,old.index('pub(crate) fn evaluate_with_selectors('))
loop=braces(parent,parent.index('while link_index <'))
header=loop[:loop.index('#[cfg')]
marker='#[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]'
branch=braces(loop,loop.index(marker))
original=header+branch+'link_index += 1;'
trans=compact(original)
trans=trans.replace('link_weight(link,append_index,variant)','NKR_copy_weight(link,append_index,variant,l)')
trans=trans.replace('accumulate_endpoint_selector_tensor_basis(&mutselector_tensor_scratch,','NKR_copy_endpoint(scratch,')
trans=trans.replace('selectors,);','selectors,l);')
actual=braces(code,code.index('fn NKR_copy_link('));actual=actual[:actual.rfind('link_index')]
assert trans==compact(actual),'Frozen218 per-link window differs beyond child substitutions'
tail=parent[parent.rfind('let (values, weights) ='):]
start=tail.index('row.producer_values');stop=tail.index('    let active =')
assignments=tail[start:tail.rfind('}',0,stop)]
rest=tail[stop:]
originalTail=assignments+rest
transTail=compact(originalTail)
transTail=transTail.replace('selectors.active()','NKR_copy_active(selectors,l)')
transTail=transTail.replace('active.mul(copy_residual(row,h1_z,chi))','NKR_copy_mul(active,NKR_copy_residual(row,h1_z,chi,l),l)')
tailActual=braces(code,code.index('fn NKR_copy_tail('))
assert transTail==compact(tailActual),'Frozen218 post220 tail differs beyond child substitutions'
name='crates/aspis-statement/src/pool_v1/NKR_SumCopy_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_SumCopy_native.rs"]\nmod NKR_copy_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_SumCopy_native.patch').write_text(patch)
(E/'NKR_SumCopy_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,original_link=original,translated_link=trans,harness_link=actual,original_tail=originalTail,translated_tail=transTail,harness_tail=tailActual,identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
