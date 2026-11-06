from pathlib import Path
import json
E=Path(__file__).resolve().parent;D=E/'NLI_generated'
order='running alpha transcript claims terminalReply terminal low high blind mask record25 extra product partialValue extraCell masked stateBefore z0 record26 beforeZ1 z1 payload root'.split()
types=dict(running='Q',alpha='Alpha',transcript='r1_wire.SemanticTranscript H',claims='Claims',terminalReply='core.result.Result Q aspis_core.state_only_prefix.r0.Error',terminal='Q',low='Low',high='High',blind='Q',mask='Q',record25='r1_wire.ValidatedRecord',extra='Words',product='Q',partialValue='Q',extraCell='Q',masked='Q',stateBefore='Array U8 32#usize',z0='Point',record26='r1_wire.ValidatedRecord',beforeZ1='Words',z1='Point',payload='Slice U8',root='Array U8 32#usize')
# Event, bindings, reads, writes, branch kind. Explicit transcription of NLC step.
A=[
('rounds',['let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript'],[],{'running':'v.1','alpha':'v.2.1','transcript':'v.2.2'},'result'),
('mark2',['VerifyPrefix.mark none 2#u8'],[],{},'plain'),
('claims',['let r ← (IDa_Deployed.boundaries i.reservation).claims i.prefix1'],[],{'claims':'v'},'result'),
('original',[],[],{},'plain'),
('terminal',['let r ← (IDa_Deployed.boundaries i.reservation).terminal i.publicValue claims alpha i.challenges'],['claims','alpha'],{'terminalReply':'r'},'plain'),
('mapPublic',['let r ← core.result.Result.map_err (FinishModel.closureFn11 i.digest) terminalReply ()'],['terminalReply'],{'terminal':'v'},'result'),
('mark3',['VerifyPrefix.mark none 3#u8'],[],{},'plain'),
('lowArray',['let low ← (IDa_Deployed.boundaries i.reservation).fromFn 16#usize (FinishModel.closureFn9 i.digest) claims'],['claims'],{'low':'low'},'plain'),
('highArray',['let high ← (IDa_Deployed.boundaries i.reservation).fromFn 10#usize (FinishModel.closureFn5 i.digest) claims'],['claims'],{'high':'high'},'plain'),
('blind',['let row ← Array.index_usize claims 0#usize','let blind ← Array.index_usize row 27#usize'],['claims'],{'blind':'blind'},'plain'),
('alpha',[],[],{},'plain'),
('mask',['let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha'],['low','high','blind','alpha'],{'mask':'mask'},'plain'),
('record25a',['let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8'],[],{'record25':'v'},'result'),
('decode25',['let r ← NJM_RoundJoin.R.decode 29#usize record25 87#usize'],['record25'],{'extra':'v'},'result'),
('multiply',['let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal'],['terminal'],{'product':'product'},'plain'),
('addMask',['let partialValue ← (IDa_Deployed.boundaries i.reservation).add mask product'],['mask','product'],{'partialValue':'partialValue'},'plain'),
('extra28',['let extraCell ← Array.index_usize extra 28#usize'],['extra'],{'extraCell':'extraCell'},'plain'),
('addExtra',['let masked ← (IDa_Deployed.boundaries i.reservation).add partialValue extraCell'],['partialValue','extraCell'],{'masked':'masked'},'plain'),
('terminalGuard',['let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked'],['running','masked'],{},'Terminal'),
('mark4',['VerifyPrefix.mark none 4#u8'],[],{},'plain'),
('stateBefore',['let stateBefore ← r1_wire.SemanticTranscript.impl.state i.digest transcript'],['transcript'],{'stateBefore':'stateBefore'},'plain'),
('record25b',['let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8'],[],{'record25':'v'},'result'),
('circle0',['let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript record25'],['transcript','record25'],{'z0':'v','transcript':'t1'},'resultPair'),
('record26a',['let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8'],[],{'record26':'v'},'result'),
('decode26',['let r ← NJM_RoundJoin.R.decode 29#usize record26 0#usize'],['record26'],{'beforeZ1':'v'},'result'),
('record26b',['let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8'],[],{'record26':'v'},'result'),
('circle1',['let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript record26'],['transcript','record26'],{'z1':'v','transcript':'t1'},'resultPair'),
('mark5',['VerifyPrefix.mark none 5#u8'],[],{},'plain'),
('circleGuard',['let reject ← FinishModel.pointEq z0 z1'],['z0','z1'],{},'EqualCirclePoints'),
('payload2',['let r ← FinishModel.payload i.prefix1 2#u8'],[],{'payload':'v'},'result'),
('rootCopy',['let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload','let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r'],['payload'],{'root':'root'},'plain')]
# Existing checked final leaf; generator writes new ladder with uniform arguments.
live=['alpha','transcript','claims','extra','stateBefore','z0','beforeZ1','z1','root']; live=[f for f in order if f in live]
params=lambda fs:' '.join(f'({f} : {types[f]})' for f in fs)
args=lambda fs,subst={}: ' '.join('('+subst.get(f,f)+')' for f in fs)
record=lambda fs:'{l with '+', '.join(f'{f}:=some {f}' for f in fs)+'}' if fs else 'l'
meta={}
for idx,(ev,bindings,reads,writes,kind) in reversed(list(enumerate(A))):
 next_ev=A[idx+1][0] if idx+1<len(A) else 'verified'
 next_live=live; live=[f for f in order if f in (set(next_live)-set(writes))|set(reads)]
 name='NLI_Suffix_'+ev; next_name='NLI_Suffix_'+next_ev if next_ev!='verified' else 'NLI_TailVerified'
 next_fn='suffix_'+next_ev if next_ev!='verified' else 'tailVerified'
 if next_ev=='verified':
  next_live=['root','alpha','claims','extra','beforeZ1','stateBefore','z0','z1','transcript']
 cont=f'{next_fn} i {args(next_live,writes)}'
 body='\n'.join(' '+s for s in bindings)
 if kind.startswith('result'):
  body+='\n match r with\n | .Ok v => '+cont+'\n | .Err error => pure (.Err error)'
 elif kind=='plain':body+='\n '+cont
 else:body+='\n if reject then pure (.Err r1_wire.Error.'+kind+') else '+cont
 n=34-idx
 proof=''' rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_'''+ev+'''
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
'''
 # Deterministic common-call congruence, then the SAME updated local record.
 before={f:f for f in live};after={**before,**writes}
 afterbase='{l with '+', '.join(f'{f}:=some {value}' for f,value in after.items())+'}' if after else 'l'
 nexthm=next_ev if next_ev!='rootCopy' else 'rootCopy_uniform'
 call=f'{nexthm} i ({afterbase}) {args(next_live,writes)}'
 for j,binding in enumerate(bindings):
  proof+=' apply NLI_Notation.congr_bind\n'
  if kind=='resultPair':proof+=' rintro ⟨r,t1⟩\n'
  else:
   var=binding.split(' ←')[0].replace('let ','') if binding.startswith('let ') else 'ignored'
   proof+=' intro '+var+'\n'
  proof+=' try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]\n'
 if kind.startswith('result'):
  proof+=' cases r with\n | Ok v => exact '+call+'\n | Err error => rfl\n'
 elif kind=='plain':proof+=' exact '+call+'\n'
 else:proof+=' cases reject with\n | false => exact '+call+'\n | true => rfl\n'
 s=f'''import {next_name}
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_{ev} {{H : Type}} (i : Input H) {params(live)} : Code (Out H) := do
{body}
theorem {ev} {{H : Type}} (i : Input H) (l : Locals H) {params(live)} :
 run (fold {n} {{input:=i,next:=.{ev},locals:={record(live)}}}) = run (suffix_{ev} i {args(live)}) := by
{proof}#print axioms {ev}
end AspisR1.NLI_Source
end
'''
 # Keep already authored root separate; this uniform root gets own theorem name.
 if ev=='rootCopy':s=s.replace('theorem rootCopy','theorem rootCopy_uniform').replace('#print axioms rootCopy','#print axioms rootCopy_uniform')
 if next_ev=='rootCopy':s=s.replace('| (apply rootCopy)','| (apply rootCopy_uniform)')
 (D/(name+'.lean')).write_text(s)
 meta[ev]=dict(module=name,live=live,next=next_ev,n=n)
(E/'NLI_SUFFIX_PLAN.json').write_text(json.dumps(meta,indent=2))
print(json.dumps({'generated':len(A),'first':'verified then rootCopy','scope':'source-only; live variables computed backwards'}))
