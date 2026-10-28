"""Factor unchanged extracted decoder continuations at named digest returns."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin29-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=json.loads((E/'focused-project-sources.json').read_text())['AspisR1TerminalDecoder.Funs'];fn='pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1'
a=s.index('def '+fn+' (');b=s.index('\n/--',a);original=s[a:b];lines=original.split(' := do\n',1)[1].splitlines()
indices=[0,4,8,12,16,20];bounds={}
for n in indices:
 v='val'+(str(n) if n else '')
 i=next(i for i,l in enumerate(lines) if l.strip()=='| core.ops.control_flow.ControlFlow.Continue '+v+' =>')
 indent=len(lines[i])-len(lines[i].lstrip());j=i+1
 while j<len(lines) and (not lines[j].strip() or len(lines[j])-len(lines[j].lstrip())>indent):j+=1
 bounds[n]=(i+1,j)

def args(n):return ['val']+['val'+str(i) for i in range(1,n+1)]
def params(n):return '(bytes : Slice U8) ('+' '.join(args(n))+' : Array U32 8#usize)'
def call(n):return 'PV_RunJoin_DecoderStage'+str(n)+'29.run bytes '+' '.join(args(n))
def fragment(start,end,nextn=None):
 result=lines[start:end].copy()
 if nextn is not None:
  i,j=bounds[nextn];indent=len(lines[i])-len(lines[i].lstrip())
  assert start<=i<j<=end
  result[i-start:j-start]=[' '*indent+call(nextn)]
 pad=min(len(l)-len(l.lstrip()) for l in result if l.strip())
 return '\n'.join('  '+l[pad:] for l in result)
records=[]
for idx in range(len(indices)-1,-1,-1):
 n=indices[idx];nextn=indices[idx+1] if idx+1<len(indices) else None
 module='PV_RunJoin_DecoderStage'+str(n)+'29';ns='R1Z.'+module
 body=fragment(*bounds[n],nextn)
 imports='import R1Z.PV_RunJoin_HeadControl29\n'+('import R1Z.PV_RunJoin_DecoderStage'+str(nextn)+'29\n' if nextn is not None else '')
 # A small generic Try inversion is proved independently of the decoder.
 imports+='import R1Z.PV_RunJoin_ResultDomain28\n'
 theorem='''
theorem branch_continue {α ε : Type} (r : core.result.Result α ε) (a : α)
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue a)) : r = .Ok a := by
  cases r with
  | Ok b => cases h; rfl
  | Err e => cases h
#print axioms branch_continue
''' if nextn is None else ''
 implicit='{bytes : Slice U8} {'+' '.join(args(n))+' : Array U32 8#usize}'
 tail=('    | exact PV_RunJoin_DecoderStage'+str(nextn)+'29.validated h\n') if nextn is not None else ''
 text=f'''{imports}set_option autoImplicit false
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z
{('open PV_RunJoin_DecoderStage2029' if nextn is not None else '')}

/-- Unchanged extracted continuation after canonical digest {n}. -/
def run {params(n)} : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
{body}
{theorem}
theorem validated {implicit} {{snapshot : PoolV1PairLiveSnapshotV1}}
    (h : run bytes {' '.join(args(n))} = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
{tail}    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end {ns}
'''
 p=L/(module+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,p
 else:p.write_text(text)
 records.append(dict(module=module,original_start=bounds[n][0],original_end=bounds[n][1],next=nextn,sha256=hashlib.sha256(text.encode()).hexdigest()))
# The header now ends at the root digest continuation, leaving all original
# outer residual branches intact. Only the extracted suffix is factored.
module='PV_RunJoin_DecoderPrefix29';ns='R1Z.'+module;body=fragment(0,len(lines),0)
text=f'''import R1Z.PV_RunJoin_DecoderStage029
set_option autoImplicit false
namespace {ns}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z.PV_RunJoin_DecoderStage2029

def run (bytes : Slice U8) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
{body}

/-- Pure continuation factoring of the authoritative decoder, for all bytes.
No native body or primitive operation is replaced. -/
theorem source (bytes : Slice U8) : run bytes = decode_pool_v1_pair_live_snapshot_v1 bytes := by
  rfl
#print axioms source

theorem validated {{bytes : Slice U8}} {{snapshot : PoolV1PairLiveSnapshotV1}}
    (h : run bytes = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage029.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (R1Z.PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (R1Z.PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end {ns}
'''
p=L/(module+'.lean')
if '--check' in sys.argv:assert p.read_text()==text,p
else:p.write_text(text)
if '--check' not in sys.argv:(E/'decoder-stages.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(original.encode()).hexdigest(),stages=records),indent=2)+'\n')
print('decoder stages', 'checked' if '--check' in sys.argv else 'generated')
