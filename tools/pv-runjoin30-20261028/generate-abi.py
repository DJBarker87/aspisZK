from pathlib import Path
import json,re,subprocess,sys,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin30-20261028'
pin=json.loads((R/'evidence/pv-runjoin29-20261028/focused-resolution.json').read_text())['resolved']['R1Z.BuilderAdmissionExtracted']
a=subprocess.check_output(['git','cat-file','blob',pin['git_blob']]).decode()
f=(L/'BuilderForestAdmissionPort.lean').read_text();o=(E/'pv30-outer-aeneas-03-generated/Types.lean').read_text()
text='''import R1Z.PV_RunJoin_OuterTypes30
import R1Z.BuilderAdmissionCommon
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OuterABI30
open Aeneas Aeneas.Std Result
open PV_RunJoin_Outer30
'''
F='R1Z.BuilderForestAdmissionPort.';A='AspisBuilderAdmissionSource.';O='PV_RunJoin_Outer30.'
# Record conversions preserve each named field without arithmetic or validation.
records=[('membership','pool_v1.payment_relation.PoolV1MembershipWitnessV1',['siblings','index']),('leaf','pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1',['first_commitment','second_occupied','second_commitment','second_occupancy_inverse']),('pair','pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1',['nullifier_key','salt','value','pair_leaf','selected_second','membership']),('input','pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1',['pair','super_root_siblings','super_root_directions']),('note','pool_v1.payment_relation.PoolV1OutputNoteWitnessV1',['owner_key','salt','value']),('snapshot','pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1',['pool','deployment_domain','sequence','next_pair_index','current_root','frontier']),('public','pool_v1.pair_forest_trace.ForestPublic',['anchor','nullifier','recipient_commitment','change_commitment','asset']),('compilation','pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1',['trace','semantic_c1','public_statement'])]
nested={'pair_leaf':'leaf','membership':'membership','pair':'pair'}
for n,t,fields in records:
 for direction,src,dst in [('ToForest',O,F),('FromForest',F,O)]+([('ToAdmission',O,A)] if n in ['membership','leaf','pair'] else []):
  text+=f'\ndef {n}{direction} (x : {src+t}) : {dst+t} where\n'
  for field in fields:
   value= nested[field]+direction+' x.'+field if field in nested else 'x.'+field
   text+=f'  {field} := {value}\n'
 if n in ['membership','leaf','pair','input','note','snapshot','public','compilation']:
  text+=f'\ntheorem {n}_roundtrip (x : {F+t}) : {n}ToForest ({n}FromForest x) = x := by cases x; rfl\n#print axioms {n}_roundtrip\n'
text+='''
def contextToAdmission (x : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentRelationContextV1 where
  runtime_binding := ⟨x.runtime_binding.pool,x.runtime_binding.deployment_domain,
    x.runtime_binding.anchor_sequence,x.runtime_binding.anchor_root,x.runtime_binding.asset_id⟩
  spent_nullifiers := x.spent_nullifiers
'''
def enum(src,typ):
 m=re.search(r'inductive '+re.escape(typ)+r' where(.*?)(?=\n/--|\nend )',src,re.S);assert m,typ
 return [(m[1],m[2].count('→')) for m in re.finditer(r'^\| (\w+) :(.*?)(?=\n\||\Z)',m[1],re.S|re.M)]
for suffix,src,prefix in [('FromForest',f,F),('FromAdmission',a,A)]:
 for n,t,code in [('format','pool_v1.payment_relation.PoolV1PaymentStatementFormatError',src),('leafError','pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1',src),('treeError','pool_v1.incremental_merkle.PoolV1TreeError',src),('error','pool_v1.pair_trace.PoolV1PairTraceErrorV1',src)]:
  target=F+t if n=='treeError' else O+t
  text+=f'\ndef {n}{suffix} : {prefix+t} → {target}\n'
  for name,arity in enum(code,t):
   args=['v'+str(i) for i in range(arity)];rhs=args.copy()
   if name in ['Statement','PairLeaf','Tree']:
    rhs=[dict(Statement='format',PairLeaf='leafError',Tree='treeError')[name]+suffix+' v0']
   text+='  | .'+name+(' '+' '.join(args) if args else '')+' => .'+name+(' ('+') ('.join(rhs)+')' if rhs else '')+'\n'
# Forest errors return to the same source type: inverse and injectivity audit.
for n,t in [('format','pool_v1.payment_relation.PoolV1PaymentStatementFormatError'),('leafError','pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1'),('error','pool_v1.pair_trace.PoolV1PairTraceErrorV1')]:
 text+=f'\ndef {n}ToForest : {O+t} → {F+t}\n'
 for name,arity in enum(o,t):
  args=['v'+str(i) for i in range(arity)];rhs=args.copy()
  if name in ['Statement','PairLeaf']:rhs=[dict(Statement='format',PairLeaf='leafError')[name]+'ToForest v0']
  text+='  | .'+name+(' '+' '.join(args) if args else '')+' => .'+name+(' ('+') ('.join(rhs)+')' if rhs else '')+'\n'
text+='\nend R1Z.PV_RunJoin_OuterABI30\n'
for v in ['PoolV1PaymentStatementFormatError','PoolV1PairLeafErrorV1','PoolV1PairTraceErrorV1']:
 for ns in ['pool_v1.payment_relation.','pool_v1.pair_tree_profile.','pool_v1.pair_trace.']:
  text=text.replace(O+ns+v,O+ns+'PV30_'+v)
p=L/'PV_RunJoin_OuterABI30.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
print('ABI generated' if '--check' not in sys.argv else 'ABI checked')
