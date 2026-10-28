"""Expose the exact decoded return to an arbitrary continuation predicate."""
from pathlib import Path
import json,re,sys,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin30-20261028';rows=[]
nums=[20,16,12,8,4,0,'Prefix']
for k,n in enumerate(nums):
 source='PV_RunJoin_Decoder'+('Prefix29' if n=='Prefix' else 'Stage'+str(n)+'29')
 module='PV_RunJoin_Codec'+('Prefix' if n=='Prefix' else 'Stage'+str(n))+'Continuation30';ns='R1Z.'+module
 s=(L/(source+'.lean')).read_text();start=s.index('def run ');end=start+re.search(r'\n\n(?:/--|theorem )',s[start:]).start()
 original=s[start:end];header,body=original.split(' := do\n',1);body=body.rstrip()
 params=header[len('def run '):header.index(' : Result (core.result.Result')]
 vals=[] if n=='Prefix' else ['val']+['val'+str(i) for i in range(1,n+1)]
 args='bytes'+(' '+' '.join(vals) if vals else '')
 nextmodule='PV_RunJoin_CodecStage'+str(nums[k-1])+'Continuation30' if k else None
 nextsource='PV_RunJoin_DecoderStage'+str(nums[k-1])+'29' if k else None
 b=re.sub(r'let (\w+) ← (.*)',lambda m:'∃ '+m[1]+', ('+m[2]+') = ok '+m[1]+' ∧',body)
 b=re.sub(r'ok \(core.result.Result.Err [^\n]+\)','False',b)
 b=re.sub(r'ok \(core.result.Result.Ok ([^\n]+)\)',lambda m:'post ('+m[1]+')',b)
 b=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual [^\n]+','False',b)
 if nextsource:b=re.sub(re.escape(nextsource)+r'\.run ([^\n]+)',lambda m:nextmodule+'.Path '+m[1]+' post',b)
 imports=f'import R1Z.{source}\nimport R1Z.PV_RunJoin_CodecContinuationBase30\nimport R1Z.PV_RunJoin_BranchDomain28\n'+(f'import R1Z.{nextmodule}\n' if nextmodule else '')
 rules='bind_wp,ite_wp,ok_wp,accepts,residual_accepts'+(','+nextmodule+'.path_wp' if nextmodule else '')
 text=f'''{imports}set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path {params} (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
{b}

theorem path_wp {params} (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp ({source}.run {args}) (accepts post) ↔ Path {args} post := by
  unfold {source}.run Path
  simp only [{rules}]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [{rules}])
#print axioms path_wp
end {ns}
'''
 p=L/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
 rows.append(dict(module=module,source_module=source,source_fragment_sha256=hashlib.sha256(original.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' not in sys.argv:(E/'codec-continuation-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
print('codec continuations','checked' if '--check' in sys.argv else 'generated')
