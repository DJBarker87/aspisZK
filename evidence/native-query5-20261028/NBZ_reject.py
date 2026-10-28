from pathlib import Path
import json,difflib,re
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_inherited_native.rs').read_text().replace('NBW_','NBZ_RJ_')
# Existing native callback/primitive contracts and KMX attributes are retained.
# Only the two timed-out gates' setup is split into scalar initialization and
# the same original actual query call; every full carrier remains initialized.
base=Path('/tmp/NBZ_windows.rs').read_text()
a=base.index('fn NBZ_raw(');b=base.index('fn NBZ_cap<');helpers=base[a:b].replace('NBZ_raw','NBZ_RJ_owned_raw').replace('NBZ_weights','NBZ_RJ_owned_weights').replace('NBZ_lines','NBZ_RJ_owned_lines').replace('NBZ_inverses','NBZ_RJ_owned_inverses')
s+='\n'+helpers+'\n'
def span(name):
 p=s.index('fn '+name+'(');a=s.index('{',p);b=a+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return p,b
rows=[];extra=[]
for name in ['NBZ_RJ_actual_query_reject','NBZ_RJ_full_proof_actual_reject']:
 p,b=span(name);a=s.rfind('#[kani::proof]',0,p);attrs=s[a:p];body=s[p:b]
 # Full arbitrary allocated carriers, including arbitrary successful capacities.
 header='''
 let ac:usize=kani::any();kani::assume(ac>=64&&ac<=isize::MAX as usize/core::mem::size_of::<K>());
 let bc:usize=kani::any();kani::assume(bc>=64&&bc<=isize::MAX as usize/core::mem::size_of::<[u64;4]>());
'''
 body=body.replace('{','{'+header,1)
 body,n=re.subn(r'weights:Vec::from\(\[.*?\]\)','weights:NBZ_RJ_owned_weights(ac)',body,count=1,flags=re.S);assert n==1
 body,n=re.subn(r'raw:Vec::from\(\[.*?\]\)','raw:NBZ_RJ_owned_raw(bc)',body,count=1,flags=re.S);assert n==1
 body=body.replace('let mut queries=[0;22];','let mut queries:[u32;22]=kani::any();')
 body=body.replace('roots:[[0;32];2]','roots:kani::any()').replace('gamma:E::ZERO','gamma:NBZ_RJ_any_e()').replace('kappa:E::ZERO','kappa:NBZ_RJ_any_e()').replace('rho:K::ZERO','rho:NBZ_RJ_any_e().c0()').replace('claim:E::ZERO','claim:NBZ_RJ_any_e()').replace('state:[0;32]','state:kani::any()')
 body=body.replace('semantic_alpha:[K::ZERO;10]','semantic_alpha:['+','.join(['NBZ_RJ_any_e().c0()']*10)+']')
 body=body.replace('z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2]','z:['+','.join(['SecureCirclePoint{x:NBZ_RJ_any_e().c0(),y:NBZ_RJ_any_e().c0()}']*2)+']')
 # Geometry may carry any initialized contents; the overapproximating child
 # callback validates its exact input pointer. This is a routing/error cut,
 # not a claim that the geometry/fold callback has been instantiated.
 body=body.replace('let geometry=QueryGeometry{start:kani::any(),inverses:Vec::new(),line_z:Vec::new()};','''let gc:usize=kani::any();kani::assume(gc>=10&&gc<=isize::MAX as usize/core::mem::size_of::<[M31;5]>());
 let lc:usize=kani::any();kani::assume(lc>=10&&lc<=isize::MAX as usize/core::mem::size_of::<M31>());
 let geometry=QueryGeometry{start:0,inverses:NBZ_RJ_owned_inverses(gc),line_z:NBZ_RJ_owned_lines(lc)};''')
 body,n=re.subn(r'let geometry=QueryGeometry\{.*?\};', '''let gc:usize=kani::any();kani::assume(gc>=10&&gc<=isize::MAX as usize/core::mem::size_of::<[M31;5]>());
 let lc:usize=kani::any();kani::assume(lc>=10&&lc<=isize::MAX as usize/core::mem::size_of::<M31>());
 let geometry=QueryGeometry{start:0,inverses:NBZ_RJ_owned_inverses(gc),line_z:NBZ_RJ_owned_lines(lc)};''',body,count=1,flags=re.S);assert n==1
 new=name+'_scalar_setup';body=body.replace('fn '+name+'(','fn '+new+'(',1)
 extra.append(attrs+body);rows.append(dict(harness='verifier::candidate::NBZ_reject::'+new,case=name,negative=False,scope='conditional native error/routing cut, child semantic bindings remain explicit'))
 wrong=body.replace('assert!(matches!(result,Err(Error::Query)))','assert!(matches!(result,Err(Error::Parse)))',1).replace('fn '+new+'(','fn '+new+'_negative(',1)
 assert wrong!=body
 extra.append(attrs+wrong);rows.append(dict(harness='verifier::candidate::NBZ_reject::'+new+'_negative',case=name,negative=True))
s+='\n'+'\n'.join(extra)+'\n'
Path('/tmp/NBZ_reject_generated.rs').write_text(s)
(E/'NBZ_reject.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_reject.rs')))
(E/'NBZ_REJECT_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
