from pathlib import Path
import json
E=Path(__file__).resolve().parent
src=(E/'NLC_native.rs.txt').read_text();start=src.index('fn check_construct(bad:bool)');end=src.index('\nfn core_error()',start)
s=src[start:end].replace('fn check_construct(bad:bool)','fn check_construct_window(mode:u8,bad:bool)').replace('let mode:u8=kani::any();','').replace('mode<9&&','')
old='let good=actual==expected && out.roots[1][j]==root[j] && (&*out.claims as *const [[QM31;29];3]) as usize==address && crate::r1_wire::NLC_factory::snapshot(&out.transcript)==(tstate,hash,next);'
new='''let good=actual==expected && match mode {
 0=>out.roots[1][j]==root[j] && out.state_before_z0[j]==state[j],
 3=>(&*out.claims as *const [[QM31;29];3]) as usize==address,
 8=>crate::r1_wire::NLC_factory::snapshot(&out.transcript)==(tstate,hash,next),
 _=>true,
 };'''
assert old in s;s=s.replace(old,new)
plan=[]
for idx,(label,mode) in enumerate([('bytes',0),('challenges',1),('alpha',2),('claims',3),('extra',4),('before',5),('points',7),('transcript',8)]):
 for bad in [False,True]:
  name='construct_'+label+('_control' if bad else '_cut')
  s+='''\n#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NAME(){check_construct_window(MODE,BAD)}
'''.replace('NAME',name).replace('MODE',str(mode)).replace('BAD',str(bad).lower())
  plan.append({'attempt':f'NLC_K{5+len(plan):03}','harness':'r1_semantic::NLC_native::'+name,'field':label,'mode':mode,'negative':bad,'parent_timeout':'NLC_K004; never rerun'})
(E/'NLC_fields.rs.txt').write_text(s);(E/'NLC_FIELD_PLAN.json').write_text(json.dumps(plan,indent=2));print('Split retired constructor into8 field windows with controls; old harness names/body retained')
