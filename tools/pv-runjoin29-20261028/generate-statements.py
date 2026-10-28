"""Emit exact success paths of EJR-resolved native statement validators."""
from pathlib import Path
import json,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028'
s=json.loads((E/'focused-project-sources.json').read_text())['AspisR1TerminalDecoder.Funs']
rows=[]
for label,fn,typ in [('Common','validate_common','CommonPublicV1'),('Withdrawal','validate_pool_v1_withdrawal_public_v1','PoolV1WithdrawalPublicV1'),('Transfer','validate_pool_v1_private_transfer_public_v1','PoolV1PrivateTransferPublicV1')]:
 start=s.index('def pool_v1.payment_relation.'+fn+' (');end=s.index('\n/--',start);original=s[start:end];body=original.split(' := do\n',1)[1]
 body=re.sub(r'let (\w+) ← (.*)',lambda m:'∃ '+m[1]+', ('+m[2]+') = ok '+m[1]+' ∧',body)
 body=re.sub(r'ok \(core.result.Result.Err [^\n]+\)', 'False',body)
 body=body.replace('ok (core.result.Result.Ok ())','True')
 body=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit \(core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError\) residual','False',body)
 arg='common' if label=='Common' else 'public1'
 module='PV_RunJoin_'+label+'Domain29';ns='R1Z.'+module
 text='''import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_ControlDomain28
set_option autoImplicit false
namespace NS
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28

/-- Exact operational success path of the pinned extracted statement validator.
Every callee result and first-error branch remains explicit. -/
def Path (ARG : pool_v1.payment_relation.TYP) : Prop :=
BODY

theorem success_iff (ARG : pool_v1.payment_relation.TYP) :
    (∃ u, pool_v1.payment_relation.FN ARG = ok (.Ok u)) ↔ Path ARG := by
  rw [success_wp]
  unfold pool_v1.payment_relation.FN Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp])
#print axioms success_iff
end NS
'''.replace('NS',ns).replace('ARG',arg).replace('TYP',typ).replace('FN',fn).replace('BODY',body.rstrip())
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
 rows.append(dict(module=module,function=fn,source_sha256=hashlib.sha256(original.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' not in sys.argv:(E/'statement-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(rows),'statement success paths')
