from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin30-20261028'
source=L/'PV_RunJoin_OuterFuns30.lean';s=source.read_text();rows=[]
for kind,fn in [('Transfer','compile_pool_v1_pair_forest_private_transfer_merged_c1_v1'),('Withdrawal','compile_pool_v1_pair_forest_withdrawal_merged_c1_v1')]:
 start=s.index('def\n  pool_v1.pair_forest_trace.'+fn+'\n');end=s.find('\n/--',start)
 if end<0:end=s.index('\nend PV_RunJoin_Outer30',start)
 head,body=s[start:end].split('  := do\n',1);body=body.rstrip().splitlines()
 for errors in [False,True]:
  label='Errors' if errors else 'Domain';ns='R1Z.PV_RunJoin_Outer'+kind+label+'30';out=[];i=0
  while i<len(body):
   line=body[i];t=line.lstrip();n=len(line)-len(t);pad=' '*n
   j=i+1
   while j<len(body) and (not body[j].strip() or len(body[j])-len(body[j].lstrip())>n):j+=1
   if t.startswith('let ') and ' ←' in t:
    binder=t[4:t.index(' ←')];expr=t.split(' ←',1)[1].strip();es=([expr] if expr else [])+[x.strip() for x in body[i+1:j]]
    out += [pad+'∃ '+binder+', (','\n'.join(pad+'  '+x for x in es),pad+') = ok '+binder+' ∧'];i=j;continue
   if t.startswith('ok (core.result.Result.'):
    expr=' '.join(x.strip() for x in body[i:j]);out.append(pad+('('+expr[len('ok ('):-1]+' = .Err error)' if errors else 'False'));i=j;continue
   if t.startswith('core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual'):
    expr=' '.join(x.strip() for x in body[i:j]);out.append(pad+('('+expr+' = ok (.Err error))' if errors else 'False'));i=j;continue
   if t.startswith('pool_v1.pair_forest_trace.compile_forest_from_copies'):
    expr='\n'.join(body[i:j]);out.append(pad+'wp (\n'+expr+'\n'+pad+') '+('(fun r => r = .Err error)' if errors else 'isRustOk'));i=j;continue
   out.append(line);i+=1
  args=head[head.index('  (public1'):head.index(' :\n  Result')]
  typ='PV30_PoolV1PairTraceErrorV1';name='PV_RunJoin_Outer'+kind+label+'30';theorem='error_iff' if errors else 'success_iff'
  text='''import R1Z.PV_RunJoin_OuterCall30
import R1Z.PV_RunJoin_RejectionProof28
set_option autoImplicit false
noncomputable section
namespace NS
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

def Path
ARGS ERRORARG : Prop :=
BODY

theorem THEOREM
ARGS ERRORARG :
    RESULT ↔ Path public1 witness context snapshot ERRORVAL := by
  rw [WP]
  unfold pool_v1.pair_forest_trace.FN Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,
    ok_ne_err,residual_eq_wp,Result.ok.injEq,Prod.exists]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,
        residual_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,Prod.exists])
#print axioms THEOREM
end NS
'''
  result='pool_v1.pair_forest_trace.'+fn+' public1 witness context snapshot = ok (.Err error)' if errors else '(∃ c, pool_v1.pair_forest_trace.'+fn+' public1 witness context snapshot = ok (.Ok c))'
  for a,b in [('NS',ns),('ARGS',args),('ERRORARG','(error : pool_v1.pair_trace.'+typ+')' if errors else ''),('ERRORVAL','error' if errors else ''),('BODY','\n'.join(out)),('THEOREM',theorem),('RESULT',result),('WP','eq_wp' if errors else 'success_wp'),('FN',fn)]:text=text.replace(a,b)
  p=L/(name+'.lean')
  if '--check' in sys.argv:assert p.read_text()==text,p
  else:p.write_text(text)
  rows.append(dict(module=name,sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' not in sys.argv:(E/'outer-domain-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),rows=rows),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(rows),'outer domains')
