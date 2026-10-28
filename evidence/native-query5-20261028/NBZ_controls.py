"""Generate matched controls by changing exactly one assertion per reached cut.
Input is the read-only inherited terminal module. No positive proof is rerun.
Only prefix renaming and one asserted expectation differ on a selected path.
"""
from pathlib import Path
import re,json,difflib,hashlib
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_inherited_native.rs').read_text().replace('NBW_','NBZ_')
def span(name):
 p=s.index('fn '+name+'(');a=s.index('{',p);b=a+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return p,b
plan=json.loads((E.parent/'native-query4-20261028/NBW_REPLAY_PLAN.json').read_text())
timeouts={'NBW_K016','NBW_K017','NBW_K018','NBW_K019','NBW_K023','NBW_K028','NBW_K034'}
rows=[];extra=[]
helpers={'NBZ_prefix_all_g':'NBZ_prefix_case','NBZ_full_proof_prefix':'NBZ_full_proof_prefix_case'}
mutations={
 'NBZ_line_geometry_routing':('assert_eq!(z.0,zs[i-start])','assert_ne!(z.0,zs[i-start])'),
 'NBZ_tail_assignment':('assert_eq!(rhs.to_limbs()[k],returned_rhs.to_limbs()[k])','assert_ne!(rhs.to_limbs()[k],returned_rhs.to_limbs()[k])'),
 'NBZ_borrowed_push_frame':('assert_eq!(raw[j][k],if i==j {reply[k]}else{before})','assert_ne!(raw[j][k],if i==j {reply[k]}else{before})'),
 'NBZ_finish_one_store':('assert_eq!(words(out[j])[k],if i<64&&i==j {returned[k]}else{before})','assert_ne!(words(out[j])[k],if i<64&&i==j {returned[k]}else{before})'),
 'NBZ_return_carriers':('assert_eq!(words(a.weights[j])[k%4],aw)','assert_ne!(words(a.weights[j])[k%4],aw)'),
 'NBZ_node_dispatch_context':('assert_eq!(NBZ_DISPATCH_CALLS,1)','assert_eq!(NBZ_DISPATCH_CALLS,2)'),
 'NBZ_wide_scalar_dispatch':('assert_eq!(y.to_limbs()[k],NBZ_SCALAR_OUTPUT[k/4][k%4])','assert_ne!(y.to_limbs()[k],NBZ_SCALAR_OUTPUT[k/4][k%4])'),
 'NBZ_basis_store_full_copy_bound':('assert_eq!(basis[i],if i==n+j {NBZ_MUL_OUT}else{old})','assert_ne!(basis[i],if i==n+j {NBZ_MUL_OUT}else{old})'),
 'NBZ_range_next_bounded':('assert_eq!(iter.end,end)','assert_ne!(iter.end,end)'),
 'NBZ_basis_initializer':('assert_eq!(basis[i],if i==0 {M31::ONE}else{M31::ZERO})','assert_ne!(basis[i],if i==0 {M31::ONE}else{M31::ZERO})'),
 'NBZ_basis_outer_after_inner':('assert_eq!(node,NBZ_MUL_OUT.double().sub(M31::ONE).0)','assert_ne!(node,NBZ_MUL_OUT.double().sub(M31::ONE).0)'),
 'NBZ_initializer_borrowed_step':('assert_eq!(raw[j][k],if old_index<64&&old_index==j {chosen}else{before})','assert_ne!(raw[j][k],if old_index<64&&old_index==j {chosen}else{before})'),
 'NBZ_horner_argument_cut':('assert_eq!(receiver.to_limbs()[k],alpha.to_limbs()[k])','assert_ne!(receiver.to_limbs()[k],alpha.to_limbs()[k])')}
for x in plan:
 if x['attempt'] in timeouts:continue
 name=x['harness'].split('::')[-1].replace('NBW_','NBZ_')
 if name=='NBZ_none_mark_native':continue
 p,b=span(name);a=s.rfind('#[kani::proof]',0,p);body=s[p:b];attrs=s[a:p]
 if name in helpers:
  helper=helpers[name];hp,hb=span(helper);hbody=s[hp:hb];old='assert_eq!(v[j].to_limbs()[k],values[j].to_limbs()[k])';new=old.replace('assert_eq!','assert_ne!')
  assert old in hbody
  extra.append(hbody.replace(helper,helper+'_negative',1).replace(old,new,1));body=body.replace(helper,helper+'_negative')
 elif name.startswith('NBZ_coeff_'):
  hp,hb=span('NBZ_coefficient_case');hbody=s[hp:hb]
  old='assert_eq!(scale.0,if which==0 {536870912}else{1073741824})' if name.endswith(('common_h0','line_h1')) else 'assert_eq!(scale.0,NBZ_SCALE_OUT[count-1])'
  new=old.replace('assert_eq!','assert_ne!');assert old in hbody
  helper=name+'_case_negative';extra.append(hbody.replace('NBZ_coefficient_case',helper,1).replace(old,new,1));body=body.replace('NBZ_coefficient_case',helper)
 else:
  old,new=mutations[name];assert old in body;body=body.replace(old,new,1)
 body=body.replace('fn '+name+'(','fn '+name+'_negative(',1)
 extra.append(attrs+body)
 rows.append(dict(attempt=f'NBZ_K{len(rows)+1:03d}',positive=x['attempt'],harness=name+'_negative',old_assertion=old,new_assertion=new,mutation='single asserted expectation; same inputs/stubs/unwind'))
s+='\n// NBZ matched negative controls; positive definitions above are unchanged.\n'+'\n\n'.join(extra)+'\n'
Path('/tmp/NBZ_native.rs').write_text(s)
(E/'NBZ_controls.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_native.rs')))
(E/'NBZ_CONTROL_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),hashlib.sha256(s.encode()).hexdigest())
