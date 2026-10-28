"""Explicit final associations and conservative corrections; no proof credit."""
import json,lzma,sys,hashlib,difflib
from pathlib import Path
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()));E=Path('evidence/pv-fscan-20261028');O=E/'classification';fs=json.loads(lzma.open(O/'functions.json.xz').read());sources=json.loads(lzma.open(O/'sources.json.xz').read())['files'];pins={x['path']:x for x in json.loads((E/'runtime-source-pins.json').read_text())['files']}
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';b=Path(p).read_bytes();assert hashlib.sha256(b).hexdigest()==pins[p]['sha256'];tree=P.parse(b)
for name in ['private_public','withdrawal_public']:
 ns=[n for n in walk(tree.root_node) if n.type=='function_item' and b[(a:=n.child_by_field_name('name')).start_byte:a.end_byte].decode()==name];assert len(ns)==1
 n=ns[0];text=b[n.start_byte:n.end_byte];assert b'#[cfg' not in text and b'cfg!' not in text
 for f,r in fs.items():
  if f.startswith('aspis_statement::pair_forest_semantic_terminal::'+name+'('):
   r.update(**{'class':'A-function'},reason='same actual frozen candidate function source used for both MIR dumps; r0/pool-v1-kernel source selection agrees, no internal cfg',source_identity='raw complete project source item byte-identical across source-verified cohorts',project_source=dict(path=p,line=n.start_point.row+1,end_line=n.end_point.row+1,item_sha256=hashlib.sha256(text).hexdigest(),file_pin=pins[p],cohort_association='same verified mirror; original nightly and deployed1.94 source dumps use this file',source_text=text.decode()))
for f,r in fs.items():
 if r['class']=='C' and f.startswith('zeroize::') and f.split('::')[1].split('(')[0] in ['atomic_fence','optimization_barrier']:
  co=next(c for c,v in r['candidates'].items() if len(v)==1);v=r['candidates'][co][0];text=sources[v['key']]['text'].splitlines(True);item=''.join(text[v['line']-1:v['end_line']]);r['diff']=''.join(difflib.unified_diff(item.splitlines(True) if co=='evidence' else [],item.splitlines(True) if co=='deployed' else [],fromfile='zeroize1.8.1',tofile='zeroize1.9.0'))
  r['selected_cfg']=dict(target_arch='x86_64',miri=False,selection='inline asm readonly/preserves_flags/nostack branch; no compiler_fence call' if co=='deployed' else 'atomic::compiler_fence(Ordering::SeqCst)')
with lzma.open(O/'functions.json.xz','wt') as h:json.dump(fs,h,indent=2)
(O/'source-corrections.json').write_text(json.dumps(dict(V242='old-only conservative alternatives private_public/withdrawal_public resolved against actual common source file; complete pure bodies identical, no internal cfg',V169='Default<T> remains an explicit theorem boundary but the concrete deployed instantiation census is absent: strict whole-row class D',V236='original parametric boundary capture starts inside the BlockBuffer type arguments; digest_blocks is a concrete library method, not a supplied callback. Keep D until its full cone is resolved.',zeroize='On deployed x86_64/miri=false the barrier selects inline asm, not compiler_fence(SeqCst). Old exact fence trace is not source-associated to1.9.0.'),indent=2)+'\n')
