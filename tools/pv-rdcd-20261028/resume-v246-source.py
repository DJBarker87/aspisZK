from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
def sha(s):return hashlib.sha256(s).hexdigest()
def toks(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
s=(R/'slice/cmp.rs').read_text();start=s.index('default fn equal(&self, other: &[B]) -> bool');brace=s.index('{',start);e=brace+1;depth=1
while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
body=s[start:e]
expected='''default fn equal(&self, other: &[B]) -> bool {
if self.len() != other.len() { return false; }
let mut idx = 0;
while idx < self.len() {
if self[idx] != other[idx] { return false; }
idx += 1;
}
true
}'''
assert toks(body)==toks(expected)
raw=(D/'resume-v246-final-original-route/generated/V246.lean').read_text();assert not re.search(r'\b(axiom|sorry|admit|implemented_by)\b',raw)
fields=re.findall(r'^  (\w+) : (.+)$',raw,re.M)
# Whole type/method source pins; source equations are not represented as a recovered original checker.
files=['slice/cmp.rs','slice/index.rs','array/equality.rs','cmp.rs','cmp/bytewise.rs']
project=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
files2=['crates/aspis-core/src/field.rs','crates/aspis-statement/src/pool_v1/pair_terminal.rs','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs']
# Compare complete typed indexing and full-range impl bodies, with impl headers
# kept separately so a const-grammar move is never mistaken for a changed method.
index_cones=[]
for marker in ['SliceIndex<[T]> for usize','SliceIndex<[T]> for ops::RangeFull']:
 blocks=[]
 for v in ['nightly-2026-06-01','1.94.1']:
  q=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/index.rs')
  text=q.read_text();a=text.index(marker);b=text.index('{',a);e=b+1;depth=1
  while depth:depth+=(text[e]=='{')-(text[e]=='}');e+=1
  block=text[b:e];blocks.append(dict(toolchain=v,text=block,token_sha256=sha('\0'.join(toks(block)).encode()),file_sha256=sha(q.read_bytes())))
 assert blocks[0]['token_sha256']==blocks[1]['token_sha256'],marker
 index_cones.append(dict(typed_impl=marker,cohorts=blocks,all_method_bodies_identical=True))
record=dict(row='V246',deployed_loop=dict(path=str(R/'slice/cmp.rs'),file_sha256=sha((R/'slice/cmp.rs').read_bytes()),body=body,body_token_sha256=sha('\0'.join(toks(body)).encode()),law='R1Z.PV_RDCD_Slice194.loop_suffix/source_model; R1Z.PV_RDCD_SliceArrayBinding.array_binding/no_index_failure'),source_pins=[dict(path=str(R/f),sha256=sha((R/f).read_bytes())) for f in files]+[dict(path=str(project/f),sha256=sha((project/f).read_bytes())) for f in files2],emitted_field_census=fields,concrete_array_instances=['[u8;32]:BytewiseEq u8 (V216 exact-source binding)','[M31;8]:generic SlicePartialEq, M31 derived eq and default ne','[[M31;8];20]:generic SlicePartialEq recursively'],source_body_changes='1.94.1 generic equal slices replaces1.98 pointer/length equal_same_length. New checked-index loop proved, with length-equality and in-range increment invariants; every ne Result failure/divergence preserved',primitive_boundary='checked indexing, immutable array-to-slice representation, Rust scalar operations/raw_eq/transmute and compiler-cohort D381/D386 retained; no new trust field',qualification='New source-law binding, not a replacement for an original structural gate. Original native route is pinned extraction at final committed selectors.')
(D/'resume-v246-final-original-route/source-binding.json').write_text(json.dumps(dict(**record,indexing_source_comparison=index_cones),indent=2)+'\n');print('Exact1.94.1 loop body and',len(fields),'emitted field/type lines pinned')
