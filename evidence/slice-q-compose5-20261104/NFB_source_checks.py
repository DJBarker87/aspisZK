"""Concrete source fissions; these checks do not infer a native verdict."""
from pathlib import Path
import re,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
PATH='crates/aspis-r1-cost-probe/src/verifier.rs'
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|==|!=|<=|>=|\+=|[^\s]',s)
def body(s,name):
 p=s.index('fn '+name+'(');a=s.index('{',p);depth=1;b=a+1
 while depth:
  if s[b]=='{':depth+=1
  if s[b]=='}':depth-=1
  b+=1
 return s[a+1:b-1]
def frozen():return subprocess.check_output(['git','show',REV+':'+PATH],cwd=R,text=True)
def check(source=None,release=None):
 source=(E/'NFB_geometry.rs.txt').read_text() if source is None else source
 release=frozen() if release is None else release
 root=body(release,'for_range');row=body(source,'NFB_row')
 guard=body(source,'NFB_guard')
 first=root[:root.index('let mut line_z_values')]
 assert tok(guard)==tok(first+'Ok(())'),'range guard/control differs'
 # Safe moves into the exact final Rust record; no constructors or copies.
 assert tok(body(source,'NFB_pack'))==tok('Ok(QueryGeometry{start,inverses,line_z:line_z_values})')
 assert tok(root[root.rindex('Ok(Self'):])==tok('Ok(Self{start,inverses,line_z:line_z_values})')
 # Erase only explicit local call logging and substitute the exact child calls.
 row=re.sub(r' NFB_row_call\([^;]*;\n','',row)
 row=row.replace('domain::Point{x:M31(replies[0]),y:M31(replies[1])}', 'crate::fast_domain::fibre_point(fibre)')
 row=row.replace('let line_x=M31(replies[2]);','let line_x=crate::fast_domain::line_node(left);')
 row=row.replace('let line_y=M31(replies[3]);','let line_y=crate::fast_domain::line_node(right);')
 row=row.replace('NFB_row_product(line_x,line_x,M31(replies[4]),log)','line_x.mul(line_x)')
 row=row.replace('Ok(values)','')
 prefix=root[root.index('let u=query'):root.index('if values.iter()')]
 # Explicitly hoist each checked constructor in original evaluation order.
 prefix=prefix.replace('let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);','let left=domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?;let line_x=crate::fast_domain::line_node(left);')
 prefix=prefix.replace('let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);','let right=domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?;let line_y=crate::fast_domain::line_node(right);')
 assert tok(row)==tok(prefix),'row evaluation/error/operand order differs'
 assert tok(body(source,'NFB_row_product'))==tok('NFB_row_call(log,4,a.0,b.0,reply.0,0);reply'),'opaque product transport changed'
 assert tok(body(source,'NFB_row_call'))==tok('log.calls[log.len]=NFB_RowCall{kind,a,b,reply,reply2};log.len+=1;'),'local log changed'
 assert tok(body(source,'NFB_resize_step'))==tok('inverse.resize(next,M31::ZERO);'),'resize operation differs'
 assert 'flat_inverse.resize(flat.len(),M31::ZERO);' in root
 for t in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','proof_for_contract','stub_verified']:
  assert t not in source,('prohibited native shape',t)
 return dict(frozen_revision=REV,path=PATH,root_sha256=hashlib.sha256(root.encode()).hexdigest(),row_erasure_sha256=hashlib.sha256(' '.join(tok(row)).encode()).hexdigest(),full_Result=True,same_final_buffers=True,field_multiplication='local opaque log, paired NFB_MulDischarge.multiplication',credit='source-only; phase native and Lean association gates still required')
if __name__=='__main__':
 import json
 print(json.dumps(check(),indent=1))
