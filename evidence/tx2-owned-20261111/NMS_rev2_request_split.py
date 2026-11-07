"""Factor the two actual request payload arms after the retired whole proof."""
from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent
raw=subprocess.check_output(['git','show','HEAD:evidence/slice-s-retarget-20261104/NFY_Part059.lean'],text=True)
a=raw.index('namespace NFY_NFD_RequestOracle');b=raw.index('\n/--',a) if '\n/--' in raw[a:] else -1
s=raw[a:];start=s.index('  := do\n');end=s.index('\ntheorem ',start)
body=s[start+2:end].rstrip()
# Trailing source theorem comment is not part of the expression.
body=body[:body.find('\n/--')] if '\n/--'in body else body
p=body.index('              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer')
w=body.index('              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal',p)
e=re.search(r'^ {8}\| core.ops.control_flow.ControlFlow.Break residual',body[w:],re.M).start()+w
pbody=body[body.index('                let s2',p):w].rstrip();wbody=body[body.index('                let s2',w):e].rstrip()
def unindent(t):return '\n'.join(line[16:] if line.startswith(' '*16)else line for line in t.splitlines())
base='pool_v1.payment_relation.'
def actual(t):
 t=re.sub(r'\btransfer\b',base+'decode_pool_v1_private_transfer_public_v1',t)
 t=re.sub(r'\bwithdrawal\b',base+'decode_pool_v1_withdrawal_public_v1',t)
 return t.replace('core.result.Result.map_err','AspisR20Request.core.result.Result.map_err')
header='''import NMS_R2RequestMaps
set_option autoImplicit false
namespace NMS_R2RequestBranches
open Aeneas Aeneas.Std Result AspisR20Request
'''
sig='''(bytes : Array U8 320#usize) : Result
 (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)'''
source=header
for n,t in [('transfer',pbody),('withdrawal',wbody)]:source+='def '+n+' '+sig+' := do\n'+''.join(' '+l+'\n'for l in actual(unindent(t)).splitlines())+'\n'
newbody=body[:p]+'''              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer => transfer bytes
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal => withdrawal bytes
'''+body[e:]
# Substitute only actual decoder call sites, never the new helper names.
newbody=newbody.replace('core.result.Result.map_err','AspisR20Request.core.result.Result.map_err')
source+='def reference '+sig+'\n  '+newbody+'''

theorem source (bytes : Array U8 320#usize) :
 reference bytes = pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes := rfl
#print axioms source
end NMS_R2RequestBranches
'''
(E/'NMS_R2RequestBranches.lean').write_text(source)
(E/'NMS_R2_REQUEST_SPLIT.json').write_text(json.dumps(dict(reference='NFY_NFD_RequestOracle.run instantiated at actual payment decoders',input_sha256=hashlib.sha256(raw.encode()).hexdigest(),retired_attempt='NMS_L417',new_shape='separate transfer/withdrawal source arms; exact source identity then independent totality proofs'),indent=2)+'\n')
for name in ['Transfer','Withdrawal']:
 t='''import NMS_R2RequestBranches
set_option autoImplicit false
namespace NMS_R2Request'''+name+'''
open Aeneas Aeneas.Std Result WP AspisR20Request
@[step] theorem total (bytes : Array U8 320#usize) :
 NMS_R2RequestBranches.'''+name.lower()+''' bytes ⦃ _ => True ⦄ := by
 unfold NMS_R2RequestBranches.'''+name.lower()+'''
   pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
 step*
 all_goals try scalar_tac
#print axioms total
end NMS_R2Request'''+name+'\n'
 (E/('NMS_R2Request'+name+'.lean')).write_text(t)
