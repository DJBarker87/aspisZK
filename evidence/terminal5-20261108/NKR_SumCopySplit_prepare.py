"""Pin replacement218 split217-args and214-sequence windows;no launch."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_SumCopySplit_native.rs.txt').read_text()
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
#217 is a CLOSED pure scalar child. Split it from its actual SAME-descriptor
#callsite;the residual native window takes that exact returned scalar.
weight='letweight=link_weight(link,append_index,variant);'
assert compact(original).count(weight)==1
trans=compact(original).replace(weight,'')
trans=trans.replace('accumulate_endpoint_selector_tensor_basis(&mutselector_tensor_scratch,','NKR_copy_endpoint(scratch,').replace('selectors,);','selectors,l);')
actual=braces(code,code.index('fn NKR_copy_split_endpoints('));actual=actual[:actual.rfind('link_index')]
assert trans==compact(actual),'214sequence differs beyond CLOSED217 removal and child substitutions'
#Reused helpers exactly equal retained original logs/stub footprint semantics.
prior=(E/'NKR_SumCopy_native.rs.txt').read_text()
for fn in ['NKR_copy_weight','NKR_copy_endpoint']:
 assert braces(code,code.index('fn '+fn+'('))==braces(prior,prior.index('fn '+fn+'('))
assert '[[u32;4];' not in code,'Nested arbitrary arrays retired'
assert '#[kani::unwind(104)]' not in code
name='crates/aspis-statement/src/pool_v1/NKR_SumCopySplit_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_SumCopySplit_native.rs"]\nmod NKR_copy_split_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_SumCopySplit_native.patch').write_text(patch)
(E/'NKR_SumCopySplit_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,original=original,translated_endpoints=trans,harness_endpoints=actual,removed_closed_scalar_call=weight,identity=True,retired='K044 whole217+214sequence nested primitive array generation',replacement='separate217 scalar descriptor args;214sequence flat primitive inputs,saved arbitrary coordinate only',source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
print('218split source pin PASS;no scope launched')
