from pathlib import Path
import re,textwrap,sys
def emit(path,text):
 if "--check" in sys.argv:
  assert path.read_text()==text,str(path)
 else:path.write_text(text)
R=Path(__file__).resolve().parents[2]
raw=(R/'docs/research/100bit-spend-path-20261013/lean/extracted-adapter-reconstruct-20261016/AspisR1AdapterReconstruct/Funs.lean').read_text()
rc='AspisR1AdapterReconstruct.';dc='AspisR1TerminalDecoder.'
def get(name):
 m=re.search(r'\ndef\s+'+re.escape(name)+r'\s+\(',raw)
 assert m,name
 return raw[m.start():raw.find('\n/--',m.end())]
for tag,area,func,typ,validate,param,fields,ret in [
 ('Snapshot','pair_tree_profile','encode_pool_v1_pair_live_snapshot_v1','PoolV1PairLiveSnapshotV1','validate_pool_v1_pair_live_snapshot_v1','snapshot',['pool','deployment_domain','sequence','next_pair_index','current_root','frontier'],'Slice U8'),
 ('Afterstate','pair_terminal','encode_pool_v1_pair_verified_afterstate_v1','PoolV1PairVerifiedAfterstateV1','validate_verified_afterstate','afterstate',['next_pair_index','next_root','next_frontier'],'Array U8 688#usize')]:
 full=f'aspis_statement.pool_v1.{area}.{func}'
 loop=full+'_loop';loopdc=loop.replace('aspis_statement.','',1)
 m='JHi_'+tag+'LoopAssociation'
 looptype='core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 8#usize))'
 outtype='Slice U8' if tag=='Snapshot' else 'Array U8 688#usize'
 s=f'''import JHi_DigestAssociation
set_option autoImplicit false
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result

theorem source (iter : {looptype}) (out : {outtype}) :
    {rc}{loop} iter out =
    {dc}{loopdc} iter out := by
  unfold {rc}{loop} {dc}{loopdc}
    {rc}{loop}.body {dc}{loopdc}.body
  simp only [JHi_DigestAssociation.encode]
  rfl
#print axioms source
end AspisR1.{m}
'''
 emit(R/'lean'/f'{m}.lean',s)
 f=get(full)
 body=f.split('core.ops.control_flow.ControlFlow.Continue _ =>',1)[1].split('| core.ops.control_flow.ControlFlow.Break residual',1)[0]
 body=textwrap.dedent(body.strip('\n')).rstrip()
 if tag=='Snapshot':body=body.replace('ok (core.result.Result.Ok (), output10)','ok output10')
 else:body=body.replace('ok (core.result.Result.Ok output8)','ok output8')
 m='JHi_'+tag+'Body'
 rawtyp=rc+f'aspis_statement.pool_v1.{area}.{typ}';dectyp=dc+f'pool_v1.{area}.{typ}'
 er='PoolV1PairLiveSnapshotErrorV1' if tag=='Snapshot' else 'PoolV1PairVerifierTransportErrorV1'
 errtyp=rc+f'aspis_statement.pool_v1.{area}.{er}'
 args=' (output : Slice U8)' if tag=='Snapshot' else ''
 call=' output' if tag=='Snapshot' else ''
 embedded='\n'.join('  '+line for line in body.splitlines())
 check='''    (size : Slice.len output=800#usize)\n''' if tag=='Snapshot' else ''
 rhs='ok (core.result.Result.Ok (),out)' if tag=='Snapshot' else 'ok (core.result.Result.Ok out)'
 s=f'''import JHi_{tag}LoopAssociation
set_option autoImplicit false
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

def decode (value : {rawtyp}) : {dectyp} :=
  ⟨{','.join('value.'+x for x in fields)}⟩

/-- Exact source byte action after successful validation, kept symbolic. -/
def body ({param} : {dectyp}){args} : Result ({ret}) := do
{embedded}

theorem source ({param} : {rawtyp}){args}
{check}    (validated : {rc}aspis_statement.pool_v1.{area}.{validate} {param}=ok (.Ok ())) :
    {rc}{full} {param}{call}=
    (body (decode {param}){call} >>= fun out=>{rhs}) := by
  unfold {rc}{full}
'''
 if tag=='Snapshot':s+='  rw [size]\n  simp only [aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,show (800#usize !=800#usize)=false from rfl,Bool.false_eq_true,↓reduceIte]\n'
 s+=f'''  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,decode,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  congr 1
#print axioms source
end AspisR1.{m}
'''
 emit(R/'lean'/f'{m}.lean',s)
