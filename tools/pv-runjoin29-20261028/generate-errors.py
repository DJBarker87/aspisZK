import subprocess
from pathlib import Path
import json,re,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028'
pin=json.loads((E/'focused-resolution.json').read_text())['resolved']['AspisR1TerminalDecoder.Funs'];s=subprocess.check_output(['git','cat-file','blob',pin['git_blob']]).decode();assert hashlib.sha256(s.encode()).hexdigest()==pin['sha256'];rows=[]
for label,fn,typ in [('Common','validate_common','CommonPublicV1'),('Withdrawal','validate_pool_v1_withdrawal_public_v1','PoolV1WithdrawalPublicV1'),('Transfer','validate_pool_v1_private_transfer_public_v1','PoolV1PrivateTransferPublicV1')]:
 start=s.index('def pool_v1.payment_relation.'+fn+' (');end=s.index('\n/--',start);original=s[start:end];body=original.split(' := do\n',1)[1]
 body=re.sub(r'let (\w+) ← (.*)',lambda m:'∃ '+m[1]+', ('+m[2]+') = ok '+m[1]+' ∧',body)
 body=re.sub(r'ok \(core.result.Result.Err ([^\n]+)\)',lambda m:'(ok (.Err '+m[1]+') : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)',body)
 body=body.replace('ok (core.result.Result.Ok ())','False')
 body=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit \(core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError\) residual',lambda m:'('+m[0]+') = ok (.Err error)',body)
 arg='common' if label=='Common' else 'public1';module='PV_RunJoin_'+label+'Errors29';ns='R1Z.'+module
 text='''import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
namespace NS
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Exact first-error paths of the pinned extracted public validator. -/
def Path (ARG : pool_v1.payment_relation.TYP)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : Prop :=
BODY

theorem error_iff (ARG : pool_v1.payment_relation.TYP)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    pool_v1.payment_relation.FN ARG = ok (.Err error) ↔ Path ARG error := by
  rw [eq_wp]
  unfold pool_v1.payment_relation.FN Path
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq])
#print axioms error_iff
end NS
'''.replace('NS',ns).replace('ARG',arg).replace('TYP',typ).replace('FN',fn).replace('BODY',body.rstrip())
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
 rows.append(dict(module=module,function=fn,source_sha256=hashlib.sha256(original.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' not in sys.argv:(E/'statement-errors-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(rows),'statement error paths')
