"""Pin deployed218 per-link and post220 tail windows against frozen source."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_LinkSplit_native.rs.txt').read_text()
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
trans=trans.replace('link_weight(link,append_index,variant)','NKR_link_weight(link,append_index,variant,l)')
trans=trans.replace('accumulate_endpoint_selector_tensor_basis(&mutselector_tensor_scratch,','NKR_link_endpoint_args(')
trans=trans.replace('selectors,);','selectors,l);')
actual=braces(code,code.index('fn NKR_link_args('));actual=actual[:actual.rfind('link_index')]
assert trans==compact(actual),'Frozen218 per-link window differs beyond child substitutions'

endpoint=braces(old,old.index('fn accumulate_endpoint_selector_tensor_basis('))
for t in ['let group = side + usize::from(endpoint.slot);','let local = row & 15;','let weight_index = COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + group_local;','scratch[weight_index]','COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]','scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local]']:
 assert t in endpoint,t
state=compact(braces(code,code.index('fn NKR_link_endpoint_state(')))
assert 'scratch[weight_index]=replies[0];scratch[pattern_index]=replies[1];' in state
assert 'letgroup=side+usize::from(endpoint.slot);' in state
assert 'letlocal=usize::from(endpoint.row)&15;' in state
assert 'letweight_index=COPY_SELECTOR_TENSOR_WEIGHT_OFFSET+usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);' in state
assert 'letpattern_index=COPY_SELECTOR_TENSOR_PATTERN_OFFSET+usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);' in state
name='crates/aspis-statement/src/pool_v1/NKR_LinkSplit_native.rs'
new=old+'\\n#[cfg(kani)]\\n#[path="NKR_LinkSplit_native.rs"]\\nmod NKR_link_split_native;\\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_LinkSplit_native.patch').write_text(patch)
(E/'NKR_LinkSplit_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),original_link=original,translated_link=trans,harness_link=actual,frozen_endpoint=endpoint,identity=True,retired='K044 full link+state TIMEOUT remains unchanged',scope='Args: actual217descriptor and both214payloads sameargs; state: arbitrary valid endpoints, two214write footprints, borrowed replies, all103coordinates, both actual pre-write input cells. Products not evaluated. Depends on CLOSED214 footprint law; no new endpoint computation credit.'),indent=2))
print('218 isolated link argument/state frozen windows PASS')
