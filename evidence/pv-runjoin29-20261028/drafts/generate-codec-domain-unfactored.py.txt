"""Exact success/error WP paths for the authoritative extracted snapshot codec."""
from pathlib import Path
import json,re,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028'
s=json.loads((E/'focused-project-sources.json').read_text())['AspisR1TerminalDecoder.Funs']
fn='pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1';start=s.index('def '+fn+' (');end=s.index('\n/--',start);original=s[start:end];body=original.split(' := do\n',1)[1]
assert not re.search(r'let \([^\n]+ ←',body),'tuple binder needs an explicit shape adapter'
body=re.sub(r'let (\w+) ← (.*)',lambda m:'∃ '+m[1]+', ('+m[2]+') = ok '+m[1]+' ∧',body)
for kind in ['Success','Error']:
 b=body
 if kind=='Success':
  b=re.sub(r'ok \(core.result.Result.Err [^\n]+\)', 'False',b)
  b=re.sub(r'ok \(core.result.Result.Ok [^\n]+\)', 'True',b)
  b=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual [^\n]+','False',b)
 else:
  b=re.sub(r'ok \(core.result.Result.Err ([^\n]+)\)',lambda m:'(ok (.Err '+m[1]+') : Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)',b)
  b=re.sub(r'ok \(core.result.Result.Ok [^\n]+\)', 'False',b)
  b=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual [^\n]+',lambda m:'('+m[0]+') = ok (.Err error)',b)
 module='PV_RunJoin_Codec'+kind+'29';ns='R1Z.'+module
 extra='' if kind=='Success' else ' (error : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1)'
 conclusion='(∃ snapshot, '+fn+' bytes = ok (.Ok snapshot)) ↔ Path bytes' if kind=='Success' else fn+' bytes = ok (.Err error) ↔ Path bytes error'
 base='success_wp' if kind=='Success' else 'eq_wp'
 rules='bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp' if kind=='Success' else 'bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq'
 text=f'''import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Exact operational {kind.lower()} path of snapshot decoding, retaining
all primitive calls, Try branches, and header/digest rejection precedence. -/
def Path (bytes : Slice U8){extra} : Prop :=
{b.rstrip()}

theorem iff_path (bytes : Slice U8){extra} :
    {conclusion} := by
  rw [{base}]
  unfold {fn} Path
  simp only [{rules}]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [{rules}])
#print axioms iff_path
end {ns}
'''
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
if '--check' not in sys.argv:(E/'codec-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(original.encode()).hexdigest(),classification='mechanical WP paths; kernel proofs are independent of generator trust'),indent=2)+'\n')
print('codec paths', 'checked' if '--check' in sys.argv else 'generated')
