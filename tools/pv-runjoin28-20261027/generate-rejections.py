from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[2]
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderForestAdmissionPort.lean';s=p.read_text();start=s.index('def pool_v1.pair_forest_trace.compile_forest_from_copies\n');end=s.index('\n#print axioms',start)
body=s[start:end].split('  := do\n',1)[1].rstrip().splitlines();out=[];i=0
while i<len(body):
 line=body[i];t=line.lstrip();n=len(line)-len(t);pad=' '*n
 if t.startswith('let ') and ' ←' in t:
  binder=t[4:t.index(' ←')];expr=t.split(' ←',1)[1].strip();j=i+1
  while j<len(body) and (not body[j].strip() or len(body[j])-len(body[j].lstrip())>n):j+=1
  es=([expr] if expr else [])+[x.strip() for x in body[i+1:j]]
  expression='\n'.join(pad+'  '+x for x in es)
  if binder in ['(b6, _)','(b7, _)']:
   b=binder[1:3];variables='('+b+' : Bool), ∃ unused';value='('+b+', unused)'
  else:variables=binder;value=binder
  out += [pad+'∃ '+variables+', (',expression,pad+') = ok '+value+' ∧'];i=j;continue
 if t.startswith('ok (core.result.Result.') or t.startswith('core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual'):
  j=i+1
  while j<len(body) and (not body[j].strip() or len(body[j])-len(body[j].lstrip())>n):j+=1
  if t.startswith('ok (core.result.Result.Ok'):out.append(pad+'False')
  else:
   term=' '.join(x.strip() for x in body[i:j]);out.append(pad+'('+term+' : Result (core.result.Result pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 pair_trace.PoolV1PairTraceErrorV1)) = ok (.Err error)')
  i=j;continue
 out.append(line);i+=1
text='''import R1Z.PV_RunJoin_ResultDomain28
import R1Z.PV_RunJoin_UniversalRecords22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerRejections28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open R1Z.BuilderForestStdPort

/-- Exact error paths of the inner compiler, including earlier-guard
precedence. Every Try residual and error constructor is retained explicitly.
This predicate contains no call to compile_forest_from_copies. -/
def Path [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out_value : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pair_forest_trace.ForestPublic) (lane_anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (error : pair_trace.PoolV1PairTraceErrorV1) : Prop :=
'''+ '\n'.join(out)+ '\nend R1Z.PV_RunJoin_CompilerRejections28\n'
q=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CompilerRejections28.lean'
if '--check' in sys.argv:assert q.read_text()==text;print('Rejection paths agree with frozen source body')
else:q.write_text(text)
