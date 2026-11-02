"""Transitive NEA support: local records, same original names and opaque products."""
from NEK_priority import *
import re
D='evidence/slice-q-compose-20261029/NEB_IMPORTED_POINT'
def path(num):return f'{D}/NEA_K{num:03}/receipt.json'
def original(num):return dict(patched_files((ROOT/D/f'NEA_K{num:03}/NEA_harness.patch').read_text()))

def context_overlay(num):
 o=original(num);p='crates/aspis-r1-cost-probe/src/fast_domain.rs';pm='crates/aspis-r1-cost-probe/src/NEA_point.rs';lm='crates/aspis-r1-cost-probe/src/NEA_line.rs';point=o[pm];line=o[lm];parent=o[p]
 # Each historical variant is decoded separately; never borrow another
 # receipt's bounds, reset or predicate.
 point=re.sub(r'^.*\bstatic\s+mut\b.*\n','',point,flags=re.M);line=re.sub(r'^.*\bstatic\s+mut\b.*\n','',line,flags=re.M)
 if 'struct PointLog' not in point:point=point.replace('use super::*;','use super::*;\n#[derive(Clone,Copy,kani::Arbitrary)] pub(super) struct PointLog{pub count:usize,pub left:[u32;2],pub right:[u32;2],pub reply:[u32;2]}',1)
 if 'struct ScalarLog' not in line:line=line.replace('use super::*;','use super::*;\n#[derive(Clone,Copy,kani::Arbitrary)] pub(super) struct ScalarLog{pub count:usize,pub x:u32,pub y:u32,pub reply:u32}',1)
 # Individual old globals and aggregate old logs have identical field maps.
 for name,field in [('COUNT','count'),('LEFT','left'),('RIGHT','right'),('REPLY','reply')]:point=re.sub(r'\b'+name+r'\b','ctx.point.'+field,point)
 point=re.sub(r'\bLOG\b','ctx.point',point)
 line=line.replace('NEA_point::LOG','ctx.point')
 for name,field in [('COUNT','count'),('LEFT','left'),('RIGHT','right'),('REPLY','reply')]:line=line.replace('NEA_point::'+name,'ctx.point.'+field)
 for name,field in [('COUNT','count'),('ARGX','x'),('ARGY','y'),('REPLY','reply')]:line=re.sub(r'\b'+name+r'\b','ctx.line.'+field,line)
 line=re.sub(r'\bLOG\b','ctx.line',line)
 for name in ['cm_mul']:
  point=point.replace('fn '+name+'(', 'fn '+name+'(ctx:&mut NEK_Context,')
 for name in ['point_post','tail_post']:point=point.replace('fn '+name+'(', 'fn '+name+'(ctx:&NEK_Context,')
 for name in ['m_mul','point_cut']:line=line.replace('fn '+name+'(', 'pub(super) fn '+name+'(ctx:&mut NEK_Context,')
 line=line.replace('fn line_post(', 'fn line_post(ctx:&NEK_Context,')
 for name in ['point_post','tail_post']:line=line.replace('NEA_point::'+name+'(', 'NEA_point::'+name+'(ctx,')
 # Fixed-signature field-product stubs become explicit local-context native
 # cuts. No multiplication executes in Kani; the original Lean laws remain.
 for textname,text in [('point',point),('line',line)]:
  text=re.sub(r'^#\[kani::stub\((?:CM31|M31)::mul,[^\n]*\)\]\n','',text,flags=re.M)
  text=re.sub(r'^#\[cfg_attr\(NEA_line_opaque,kani::stub\(fibre_point,point_cut\)\)\]\n','',text,flags=re.M)
  text=re.sub(r'(fn (?:point|line)\(\)\s*\{)',r'\1let mut ctx=NEK_Context::new();',text)
  text=text.replace('let _=fibre_point(u)','let _=fibre_point(&mut ctx,u)').replace('let _=line_node(u)','let _=line_node(&mut ctx,u)')
  if textname=='point':point=text
  else:line=text
 # Parent contract field maps preserve exactly the original modifies footprint.
 parent=parent.replace('NEA_point::LOG','ctx.point').replace('NEA_line::LOG','ctx.line')
 for name,field in [('COUNT','count'),('LEFT','left'),('RIGHT','right'),('REPLY','reply')]:parent=parent.replace('NEA_point::'+name,'ctx.point.'+field)
 for name,field in [('COUNT','count'),('ARGX','x'),('ARGY','y'),('REPLY','reply')]:parent=parent.replace('NEA_line::'+name,'ctx.line.'+field)
 for name in ['point_post','tail_post']:parent=parent.replace('NEA_point::'+name+'(u,','NEA_point::'+name+'(ctx,u,')
 parent=parent.replace('NEA_line::line_post(u,','NEA_line::line_post(ctx,u,')
 parent=parent.replace('pub fn fibre_point(u:', 'pub fn fibre_point(ctx:&mut NEK_Context,u:').replace('pub fn line_node(u:', 'pub fn line_node(ctx:&mut NEK_Context,u:')
 parent=parent.replace('let point = left.mul(right);','let point = NEA_point::cm_mul(ctx,left,right);')
 parent=parent.replace('let x = fibre_point(u).x;', 'let x = {#[cfg(NEA_line_opaque)] {NEA_line::point_cut(ctx,u)} #[cfg(not(NEA_line_opaque))] {fibre_point(ctx,u)}}.x;')
 parent=parent.replace('let square = x.mul(x);','let square = NEA_line::m_mul(ctx,x,x);')
 # The ghost initial-count domain is explicit and is established by every
 # harness's fresh local record (and by unselected call-site adapters below).
 # Existing opaque-line entry reset is retained verbatim under the field map.
 fp=parent.index('pub fn fibre_point(');lp=parent.index('pub fn line_node(')
 first=parent[:lp];second=parent[lp:]
 first=first.replace('kani::requires(u.get()<262144)', 'kani::requires(u.get()<262144 && ctx.point.count==0)')
 # The line's requires attribute occurs before its declaration, in first.
 last=first.rfind('kani::requires(u.get()<262144 && ctx.point.count==0)')
 # Distinguish line attribute by its position after the point body closing.
 if last>fp:first=first[:last]+first[last:].replace('kani::requires(u.get()<262144 && ctx.point.count==0)','kani::requires(u.get()<262144 && (cfg!(NEA_line_opaque) || (ctx.point.count==0 && ctx.line.count==0)))',1)
 parent=first+second
 ctx='''
#[cfg(kani)] #[derive(Clone,Copy,kani::Arbitrary)]
pub struct NEK_Context{pub(crate) point:NEA_point::PointLog,pub(crate) line:NEA_line::ScalarLog}
#[cfg(kani)] impl NEK_Context{pub fn new()->Self{Self{point:NEA_point::PointLog{count:0,left:[0;2],right:[0;2],reply:[0;2]},line:NEA_line::ScalarLog{count:0,x:0,y:0,reply:0}}}}
'''
 parent+='\n'+ctx
 result=root('crates/aspis-r1-cost-probe','NEA_copy','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));')
 result[p]=parent;result[pm]=point;result[lm]=line;result['crates/aspis-r1-cost-probe/src/NEA_point_reference.rs']=o['crates/aspis-r1-cost-probe/src/NEA_point_reference.rs']
 # Unselected verifier callers create fresh ghost records; erasing that first
 # argument restores each exact frozen call. They provide no caller credit.
 vp='crates/aspis-r1-cost-probe/src/verifier.rs';v=frozen(vp).decode()
 for name in ['fibre_point','line_node']:v=v.replace('crate::fast_domain::'+name+'(','crate::fast_domain::'+name+'(&mut crate::fast_domain::NEK_Context::new(),')
 result[vp]=v
 core='crates/aspis-core/src/lib.rs';result[core]=frozen(core).decode()+'\n#[cfg(kani)] mod NEK_nea_arbitrary;\n'
 result['crates/aspis-core/src/NEK_nea_arbitrary.rs']='impl kani::Arbitrary for crate::field::M31{fn any()->Self{Self(kani::any())}}\nimpl<E:kani::Arbitrary> kani::Arbitrary for crate::r0::domain::Point<E>{fn any()->Self{Self{x:kani::any(),y:kani::any()}}}\n'
 assert all('static mut' not in t for t in result.values())
 return result

def copy_overlay():return root('crates/aspis-r1-cost-probe','NEA_copy','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));')
def run():
 tests=[(17,12),(18,13),(19,17),(206,17),(207,17),(20,18),(21,29),(22,30),(204,31),(205,32)]
 for aidx,num in tests:
  a=f'NEK_K{aidx:03}';rp=path(num)
  if (E/a/'receipt.json').exists():continue
  o=copy_overlay() if num in [12,13,31,32] else context_overlay(num)
  v=publish(a,rp,o,num in [13,18,30,32],'transitive NEA support; original names/property, local explicit point/scalar logs; retained emitted product laws; no field multiplication in Kani')
  if v=='OPEN':break
if __name__=='__main__':
 if os.environ.get('NEK_PLAN_ONLY'):
  for i in [17,18,29,30]:print(i,len(context_overlay(i)))
 else:run()
