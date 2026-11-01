"""Bind the concrete copy layer; deliberately do not restore full V236."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';lib={x['relative']:x for x in json.load(open(E/'library-sources.json'))}
s=lib['slice/mod.rs']['text'];lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def body(marker):
 assert s.count(marker)==1;a=s.index(marker);b=s.index('{',a);depth=0
 for m in lex.finditer(s,b):
  if m[0]=='{':depth+=1
  elif m[0]=='}':
   depth-=1
   if not depth:return s[a:m.end()]
def tokens(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
wrapper=body('pub const fn copy_from_slice(');assert tokens(wrapper)==tokens('pub const fn copy_from_slice(&mut self,src:&[T])where T:Copy,{unsafe{copy_from_slice_impl(self,src)}}')
impl=body('const unsafe fn copy_from_slice_impl<')
assert 'if dest.len() != src.len()' in impl and 'len_mismatch_fail(dest.len(), src.len())' in impl
assert 'ptr::copy_nonoverlapping(src.as_ptr(), dest.as_mut_ptr(), dest.len())' in impl
out=dict(row='V236',status='PARTIAL ONLY; whole row suspended',source_file_sha256=lib['slice/mod.rs']['sha256'],wrapper=wrapper,implementation=impl,bindings=['PV_RDCD4_Copy194.binding/success/mismatch/source_frame','PV_RDCD4_CopyWindow194.binding/length/empty/short_position'],source_steps=['Public Copy wrapper forwards to implementation; no Clone callback is executed.','Length mismatch invokes panic before any memory write; same complete Result failure class.','Equal lengths invoke only argument-confined non-overlapping memory copy. Concrete u8 Copy; exclusive destination/source borrow supplies non-overlap; intrinsic semantics remain V370.','Buffer double slicing preserves first base<=length then count<=remaining checks. The changed window is reinserted with both untouched prefix and suffix. Empty copy retains all dead buffer bytes.'],missing='Full BlockBuffer.digest_blocks/get_pos/set_pos control-flow/ordered-callback and typed Eager split carrier transport; only the original compression callback may remain parametric.',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(E/'v236-copy-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Concrete copy source associated with passed helpers; no whole V236 credit.')
