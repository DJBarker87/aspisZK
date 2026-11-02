"""Receipt-specific inverse source projection for explicit local product logs."""
from NEK_nea import *
def function(t,name):
 start=t.index('pub fn '+name+'(');brace=t.index('{',start);i=brace+1;d=1
 while d:
  if t[i]=='{':d+=1
  elif t[i]=='}':d-=1
  i+=1
 return t[start:i]
out=[]
for a,num in [('NEK_K207',17),('NEK_K020',18),('NEK_K021',29),('NEK_K022',30)]:
 overlay=read_json(E/(a+'_overlay.json'));old=original(num);p='crates/aspis-r1-cost-probe/src/fast_domain.rs'
 for name in ['fibre_point','line_node']:
  before=function(old[p],name);after=function(overlay[p],name)
  back=after.replace('ctx:&mut NEK_Context,','')
  back=back.replace('NEA_point::cm_mul(ctx,left,right)','left.mul(right)').replace('NEA_line::m_mul(ctx,x,x)','x.mul(x)')
  back=back.replace('{#[cfg(NEA_line_opaque)] {NEA_line::point_cut(ctx,u)} #[cfg(not(NEA_line_opaque))] {fibre_point(ctx,u)}}','fibre_point(u)')
  back=back.replace('ctx.line.count','NEA_line::LOG.count' if 'NEA_line::LOG' in before else 'NEA_line::COUNT')
  assert before==back,(a,name)
  out.append(dict(attempt=a,original_receipt=path(num),function=name,original_body_sha256=sha(before.encode()),instrumented_body_sha256=sha(after.encode()),inverse_projection_equal=True,scope='local native-step/cut association; emitted multiplication, caller freshness and existing P6/D188 transport retained'))
 # Every unselected verifier adapter erases exactly to the frozen invocation.
 vp='crates/aspis-r1-cost-probe/src/verifier.rs';v=overlay[vp]
 for name in ['fibre_point','line_node']:v=v.replace('crate::fast_domain::'+name+'(&mut crate::fast_domain::NEK_Context::new(),','crate::fast_domain::'+name+'(')
 assert v==frozen(vp).decode(),a
(E/'NEK_NEA_LOCAL_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(out),'receipt-specific function inverse projections')
