from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
source=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderForestAdmissionPort.lean'
s=source.read_text(); start=s.index('def pool_v1.pair_forest_trace.compile_forest_from_copies\n'); end=s.index('\n#print axioms',start)
body=s[start:end].split('  := do\n',1)[1].rstrip().splitlines()
out=[];i=0;stages=[]
while i<len(body):
 line=body[i]; t=line.lstrip();n=len(line)-len(t);pad=' '*n
 if t.startswith('let ') and ' ←' in t:
  binder=t[4:t.index(' ←')];expr=t.split(' ←',1)[1].strip();j=i+1
  while j<len(body) and (not body[j].strip() or len(body[j])-len(body[j].lstrip())>n):j+=1
  es=([expr] if expr else [])+[x.strip() for x in body[i+1:j]]
  expression='\n'.join(pad+'  '+x for x in es)
  if binder=='(b6, _)': variables='(b6 : Bool) unused';value='(b6, unused)'
  elif binder=='(b7, _)':variables='(b7 : Bool) unused';value='(b7, unused)'
  else:variables=binder;value=binder
  out += [pad+'∃ '+variables+', (',expression,pad+') = ok '+value+' ∧']
  stages.append(dict(variable=binder,operation=' '.join(es)))
  i=j;continue
 if t.startswith('ok (core.result.Result.') or t.startswith('core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual'):
  j=i+1
  while j<len(body) and (not body[j].strip() or len(body[j])-len(body[j].lstrip())>n):j+=1
  out.append(pad+('True' if t.startswith('ok (core.result.Result.Ok') else 'False'));i=j;continue
 out.append(line);i+=1
text='''import R1Z.PV_RunJoin_UniversalRecords22
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerDomain28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open R1Z.BuilderForestStdPort

/-- A success path of the extracted INNER compiler. Each primitive result,
comparison and Try branch is explicit; this does not call the compiler or
assume its success. Outer wrapper checks are a separate obligation. -/
def Path [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out_value : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pair_forest_trace.ForestPublic) (lane_anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) : Prop :=
'''+ '\n'.join(out)+'\nend R1Z.PV_RunJoin_CompilerDomain28\n'
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CompilerDomain28.lean';p.write_text(text)
(R/'evidence/pv-runjoin28-20261027/domain-generation.json').write_text(json.dumps(dict(source=str(source.relative_to(R)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),target=str(p.relative_to(R)),stages=stages),indent=2)+'\n')
