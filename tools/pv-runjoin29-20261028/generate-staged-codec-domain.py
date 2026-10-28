"""Kernel-checked WP domains over unchanged, bounded decoder continuations."""
from pathlib import Path
import json,re,sys,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin29-20261028';rows=[]
nums=[20,16,12,8,4,0,'Prefix']
for k,n in enumerate(nums):
 source='PV_RunJoin_Decoder'+('Prefix29' if n=='Prefix' else 'Stage'+str(n)+'29')
 module='PV_RunJoin_Codec'+('Prefix' if n=='Prefix' else 'Stage'+str(n))+'Domain29';ns='R1Z.'+module
 s=(L/(source+'.lean')).read_text();start=s.index('def run ');end=s.index('\n\ntheorem',start) if '\n\ntheorem' in s[start:] else -1
 original=s[start:end];header,body=original.split(' := do\n',1)
 # Stage20 has an adjacent branch lemma, which is outside the executable body.
 body=body.rstrip()
 params=header[len('def run '):header.index(' : Result (core.result.Result')]
 vals=[] if n=='Prefix' else ['val']+['val'+str(i) for i in range(1,n+1)]
 callargs='bytes'+(' '+' '.join(vals) if vals else '')
 nextmodule='PV_RunJoin_CodecStage'+str(nums[k-1])+'Domain29' if k else None
 nextsource='PV_RunJoin_DecoderStage'+str(nums[k-1])+'29' if k else None
 stem=re.sub(r'let (\w+) ← (.*)',lambda m:'∃ '+m[1]+', ('+m[2]+') = ok '+m[1]+' ∧',body)
 paths={}
 for kind in ['success','error']:
  b=stem
  if kind=='success':
   b=re.sub(r'ok \(core.result.Result.Err [^\n]+\)', 'False',b)
   b=re.sub(r'ok \(core.result.Result.Ok [^\n]+\)', 'True',b)
   b=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual [^\n]+','False',b)
  else:
   b=re.sub(r'ok \(core.result.Result.Err ([^\n]+)\)',lambda m:'(ok (.Err '+m[1]+') : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)',b)
   b=re.sub(r'ok \(core.result.Result.Ok [^\n]+\)', 'False',b)
   b=re.sub(r'core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual [^\n]+',lambda m:'('+m[0]+') = ok (.Err error)',b)
  if nextsource:
   pattern=re.escape(nextsource)+r'\.run ([^\n]+)'
   b=re.sub(pattern,lambda m:nextmodule+('.Path ' if kind=='success' else '.ErrorPath ')+m[1]+(' error' if kind=='error' else ''),b)
  paths[kind]=b
 imports=f'import R1Z.{source}\nimport R1Z.PV_RunJoin_RejectionProof28\nimport R1Z.PV_RunJoin_BranchDomain28\n'+(f'import R1Z.{nextmodule}\n' if nextmodule else '')
 text=f'''{imports}set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Source primitives and branch guards only; no whole-decoder success premise. -/
def Path {params} : Prop :=
{paths['success']}

/-- Every first-error path retains its entire successful prefix. -/
def ErrorPath {params} (error : PoolV1PairLiveSnapshotErrorV1) : Prop :=
{paths['error']}
'''
 for kind in ['success','error']:
  extra='' if kind=='success' else ' (error : PoolV1PairLiveSnapshotErrorV1)'
  lhs=f'(∃ snapshot, {source}.run {callargs} = ok (.Ok snapshot))' if kind=='success' else f'{source}.run {callargs} = ok (.Err error)'
  rhs=f'Path {callargs}' if kind=='success' else f'ErrorPath {callargs} error'
  base='R1Z.PV_RunJoin_ResultDomain28.success_wp' if kind=='success' else 'eq_wp'
  rules='bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp' if kind=='success' else 'bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq'
  if nextmodule:rules+=','+nextmodule+('.path_wp' if kind=='success' else '.error_wp')
  text+=f'''
theorem {kind}_iff {params}{extra} : {lhs} ↔ {rhs} := by
  rw [{base}]
  unfold {source}.run {'Path' if kind=='success' else 'ErrorPath'}
  simp only [{rules}]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [{rules}])
#print axioms {kind}_iff
'''
 if n!='Prefix':
  text+=f'''
theorem path_wp {params} : wp ({source}.run {callargs}) isRustOk ↔ Path {callargs} :=
  (R1Z.PV_RunJoin_ResultDomain28.success_wp _).symm.trans (success_iff {callargs})
#print axioms path_wp

theorem error_wp {params} (error : PoolV1PairLiveSnapshotErrorV1) :
    wp ({source}.run {callargs}) (fun x => x = .Err error) ↔ ErrorPath {callargs} error :=
  (eq_wp _ _).symm.trans (error_iff {callargs} error)
#print axioms error_wp
'''
 text+='end '+ns+'\n';p=L/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
 rows.append(dict(module=module,source_module=source,source_fragment_sha256=hashlib.sha256(original.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest()))
for kind in ['Success','Error']:
 module='PV_RunJoin_Codec'+kind+'29';ns='R1Z.'+module
 extra='' if kind=='Success' else ' (error : PoolV1PairLiveSnapshotErrorV1)'
 pred='Path' if kind=='Success' else 'ErrorPath';args='bytes' if kind=='Success' else 'bytes error'
 lhs='(∃ snapshot, decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok snapshot))' if kind=='Success' else 'decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Err error)'
 theorem='success_iff' if kind=='Success' else 'error_iff'
 text=f'''import R1Z.PV_RunJoin_CodecPrefixDomain29
set_option autoImplicit false
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile

def Path (bytes : Slice U8){extra} : Prop := R1Z.PV_RunJoin_CodecPrefixDomain29.{pred} {args}

theorem iff_path (bytes : Slice U8){extra} :
    {lhs} ↔ Path {args} := by
  rw [← R1Z.PV_RunJoin_DecoderPrefix29.source]
  exact R1Z.PV_RunJoin_CodecPrefixDomain29.{theorem} {args}
#print axioms iff_path
end {ns}
'''
 p=L/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
if '--check' not in sys.argv:(E/'staged-codec-domain.json').write_text(json.dumps(rows,indent=2)+'\n')
print('staged codec domains', 'checked' if '--check' in sys.argv else 'generated')
