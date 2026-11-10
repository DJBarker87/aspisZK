import re,sys
src,out=sys.argv[1:3]
s=open(src).read().rstrip()+'\n'
FQ='FIq_Native.PRVFresh_RPu_FIq_Native04_n04'; P='PRVEq.RPu_FIq_Native04_n04'
IP='state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFn'
def th(name,fresh,gate,simp,pre='delta'):
    return f'''
set_option maxHeartbeats 200000 in
theorem {P}.{name} : @{FQ}.{fresh} = @FIq_Native.{gate} := by
  {pre} {FQ}.{fresh} FIq_Native.{gate}
  try simp only [{', '.join(simp)}]
  try rfl
  done
#print axioms {P}.{name}
'''
n=IP+'MutTupleUsizeM31.call_mut'
t=th('PCWP.'+IP+'OnceTupleUsizeM31.call_once',IP+'OnceTupleUsizeM31.call_once',IP+'OnceTupleUsizeM31.call_once',[f'{P}.{n}'])
t+=th('PCWP.'+IP+'OnceTupleUsizeM31',IP+'OnceTupleUsizeM31',IP+'OnceTupleUsizeM31',[f'{P}.PCWP.{IP}OnceTupleUsizeM31.call_once'])
t+=th('PCWP.'+IP+'MutTupleUsizeM31',IP+'MutTupleUsizeM31',IP+'MutTupleUsizeM31',[f'{P}.{n}',f'{P}.PCWP.{IP}OnceTupleUsizeM31'])
LZ='state_only_poseidon.internal_linear_lazy'
callee=[f'{P}.{LZ}.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64',f'{P}.{LZ}.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64',
 f'{P}.{LZ}.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64',f'{P}.{LZ}.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64',
 f'{P}.state_only_poseidon.extension_from_raw_limbs',f'{P}.state_only_poseidon.extension_limbs',f'{P}.poseidon2.POSEIDON2_WIDTH',
 'PRVC.Eq.'+LZ+'_loop0_loop0','PRVC.Eq.'+LZ+'_loop0','PRVC.Eq.'+LZ+'_loop1',f'{P}.field.P']
# from_fn: fresh external is the HM-D model (reducible def); gate array_from_fn_copy unfolds to the same fromFn
unf=[f'{FQ}.core.array.from_fn','FIq_Native.array_from_fn_copy']
t+=th(LZ,LZ,LZ,callee+unf)
t+=th('state_only_poseidon.internal_round','state_only_poseidon.internal_round','state_only_poseidon.internal_round',[f'{P}.{LZ}',f'{P}.state_only_poseidon.pow5'])
IIP='state_only_poseidon.interpolated_internal_pair'
t+=th(IIP,IIP,IIP,[f'{P}.PCWP.{IP}MutTupleUsizeM31',f'{P}.state_only_poseidon.internal_round',f'{P}.{IIP}.ROWS',
  f'{P}.{IIP}.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31',f'{P}.{IIP}.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31'])
# the generator's pre-existing equality for the three (same names) replaces nothing: they were comments
FQP=FQ+'.'
a=s.index('theorem PRVC.Eq.state_only_poseidon.internal_linear_lazy_loop1')
blk=s[a:]
blk=blk.replace('simp only [FIq_Native.PRVFresh_RPu_FIq_Native04_n04.state_only_poseidon.internal_linear_lazy_loop1.body','simp only [FIq_Native.array_from_fn_copy, '+FQ+'.core.array.from_fn, FIq_Native.PRVFresh_RPu_FIq_Native04_n04.state_only_poseidon.internal_linear_lazy_loop1.body')
s=s[:a]+blk
open(out,'w').write(s+t)
# heartbeat discipline: bridge lemmas and every theorem at 200000; only the inlined Aeneas emission keeps its default header
s=open(out).read()
s=s.replace('set_option maxHeartbeats 1000000','set_option maxHeartbeats 200000',1)
a=s.index('namespace PRVFresh_'); 
a=s.rfind('\n',0,s.rfind('namespace FIq_Native',0,a))+1
s=s[:a]+'set_option maxHeartbeats 1000000  -- inlined Aeneas emission only (default header)\n'+s[a:]
b=s.index('end PRVFresh_'); b=s.index('\n',s.index('end FIq_Native',b))+1
s=s[:b]+'set_option maxHeartbeats 200000  -- every theorem below\n'+s[b:]
open(out,'w').write(s)
