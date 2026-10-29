"""Read-only deployed/extractor std body comparison and explicit step map.
This is a source dossier, not automatic full std binding credit."""
from pathlib import Path
import json,hashlib,re
from run import H
roots=[Path('/home/dombarker/.rustup/toolchains')/n/'lib/rustlib/src/rust/library'for n in ['1.94.1-x86_64-unknown-linux-gnu','nightly-2026-06-01-x86_64-unknown-linux-gnu']]
specs=[('iter_next','core/src/slice/iter/macros.rs','fn next(&mut self) -> Option<$elem>'),('enumerate_next','core/src/iter/adapters/enumerate.rs','fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>'),('iter_mut_new','core/src/slice/iter.rs',"pub(super) const fn new(slice: &'a mut [T])")]
sha=lambda b:hashlib.sha256(b).hexdigest()
lex=lambda s:re.findall(r'\w+|[^\s]',re.sub(r'//[^\n]*','',s))
rows=[]
for label,rel,needle in specs:
 versions=[]
 for root in roots:
  p=root/rel;s=p.read_text();assert needle in s,(p,needle)
  a=s.index(needle);b=s.index('{',a);e=b+1;depth=1
  while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
  text=s[a:e];versions.append(dict(path=str(p),file_sha256=sha(p.read_bytes()),line=s[:a].count('\n')+1,text=text,body_sha256=sha(text.encode()),tokens_sha256=sha('\0'.join(lex(text)).encode())))
 rows.append(dict(body=label,versions=versions,token_identical=versions[0]['tokens_sha256']==versions[1]['tokens_sha256']))
out=dict(rows=rows,caller='state_only_poseidon.evaluate_state_only_poseidon_oracle_projected: four QM31 packed outputs',specialization=dict(non_zst=True,size_bytes=16,region='one valid four-element mutable array, offset 0 to 4',direction='next only; no next_back; no alias escapes; callback never reads old destination'),step_map=[dict(source='IterMut::new len, ptr, end_or_len',model='SlotPointer13 region 0; slot_end13 region; size nonzero selects end pointer',remaining='complete source pointer/borrow constructor transport'),dict(source='next: cache ptr and end; non-ZST branch pointer equality',model='same_region_end13 / slice_next13 index=4'),dict(source='next: ptr.add(1); return reference to old slot',model='cursor_increment13 + exclusive slot token; pointer intrinsic boundary V370'),dict(source='Enumerate::next: next()?; copy count; increment count; Some((i,a))',model='enumerate_next13 / enumerate_step13 / enumerate_finish13'),dict(source='callback *output = computed',model='slice_store13; back continuation retained; slot_store_binding13'),dict(source='loop exit and iterator fields cleanup',model='slice_loop_plan13 / slice_iterator_drop_total13; native cleanup source association remains')],compiler_boundary='V370 / pending owner D381,D386 retained',complete_std_binding=False)
(H/'slice-std-binding-resume13.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(rows=[dict(body=r['body'],token_identical=r['token_identical'])for r in rows],complete_std_binding=False)))
