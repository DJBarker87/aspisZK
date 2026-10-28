"""Fail-closed V228 source binding; universal claims are the named Lean laws.
This is structural (K-1 substitute), not Kani or compiler correctness.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys,ast,operator
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-b3p6-20261028';T=R/'tools/pv-b3p6-20261028'
PIN='1e826627aa39fe02569bf840efb894eaa287efcf'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def fn(s,name):
 m=re.search(r'(?:pub )?(?:const )?fn '+name+r'\b',s);assert m,name
 a=s.index('{',m.start());i=a+1;n=1
 while n:n+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[m.start():i]
def tokens(s):
 s=re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S)
 return re.findall(r'\w+|::|>=|<=|->|[^\s]',s)
forest='crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs'
tree='crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs'
profile='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
host='crates/aspis-prover/src/host_forest.rs'
root='pool_v1_pair_forest_relation_free_mask_cells_v1'
owned=(T/'v228/owned132.rs').read_text();ref=(T/'v228/reference132.rs').read_text()
records=[]
specs={forest:[root,'forest_path_aux_cell_is_used','forest_poseidon_row','forest_aux_cell_is_used','pool_v1_pair_forest_path_base_row_v1','build_pool_v1_pair_forest_copy_row_schedule_v1','endpoint_counts','link'],tree:['path_aux_cell_is_used','value_aux_cell_is_used','occupancy_aux_cell_is_used','pool_v1_pair_aux_cell_is_relation_used_v1','build_pool_v1_pair_copy_row_schedule_v1','endpoint_counts','link'],profile:['pool_v1_pair_path_base_row_v1'],host:[root,'forest_path_aux_cell_is_used','forest_poseidon_row','forest_aux_cell_is_used','materialize_mask_cells']}
for path,names in specs.items():
 s=(R/path).read_text();old=git('show',PIN+':'+path).decode();assert s==old,path
 for name in names:
  body=fn(s,name);assert not re.search(r'\bcfg\s*!|debug_assert|#\[cfg',body),(path,name)
  records.append(dict(path=path,function=name,token_sha256=sha(json.dumps(tokens(body)).encode()),source_sha256=sha(s.encode()),feature_selection_in_body=False))
for name in specs[forest][:4]:assert tokens(fn(owned,name))==tokens(fn((R/forest).read_text(),name)),name
assert not re.search(r'cfg|debug_assert',ref)
# Fixed control/data skeletons are pinned separately from the original bodies.
expected_ref=git('show','79dc9aa0bb2a352bf5ea62fe13fcc820305e2b6b:tools/pv-b3p6-20261028/v228/reference132.rs').decode()
assert ref==expected_ref
# Both traversals visit columns then rows. No sorting, dedup or reordering.
rt=tokens(fn(ref,'cells'));ht=tokens(fn((R/host).read_text(),root))
for body in [fn(ref,'cells'),fn((R/host).read_text(),root)]:
 assert body.index('while column') < body.index('while row') < body.index('if ')
assert 'out[count] = Cell' in ref and 'count += 1' in ref
assert 'cells[len] = TraceCell' in (R/host).read_text() and 'len += 1' in fn((R/host).read_text(),root)
# All three host helpers are iterator-to-index translations of the same ones.
for name in ['forest_poseidon_row','forest_aux_cell_is_used']:
 assert tokens(fn((R/host).read_text(),name))==tokens(fn((R/forest).read_text(),name))
# Resolve only scalar arithmetic constants with a closed arithmetic grammar.
const_sources="\n".join((R/p).read_text() for p in [forest,tree,profile])
expressions=dict(re.findall(r"(?:pub )?const (\w+): usize =\s*([^;]+);",const_sources))
constants={}
operations={ast.Add:operator.add,ast.Sub:operator.sub,ast.Mult:operator.mul,ast.LShift:operator.lshift}
def const_node(node):
 if isinstance(node,ast.Constant):assert type(node.value)==int;return node.value
 if isinstance(node,ast.Name):return resolve_const(node.id)
 assert isinstance(node,ast.BinOp) and type(node.op) in operations,ast.dump(node)
 return operations[type(node.op)](const_node(node.left),const_node(node.right))
def resolve_const(name):
 if name not in constants:constants[name]=const_node(ast.parse(expressions[name],mode='eval').body)
 return constants[name]
expected_constants={'POOL_V1_PAIR_TRACE_ROWS':1024,'POOL_V1_PAIR_TRACE_COLUMNS':16,'POOL_V1_PAIR_TRACE_BLOCK_ROWS':16,
 'POOL_V1_PAIR_PRIVATE_DIRECTIONS':21,'POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK':4,'POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET':1,
 'POOL_V1_PAIR_POSEIDON_ROW_END':864,'POOL_V1_PAIR_VALUE_AUX_ROW_START':960,
 'POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW':969,'POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW':970,
 'POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN':10,'POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_END':10,
 'POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1':13,'POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1':24,
 'POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1':57,'POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1':912,
 'POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1':1008,'POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1':3803}
for name,value in expected_constants.items():assert resolve_const(name)==value,(name,value,constants)
table=(R/forest).read_text().split('const POOL_V1_PAIR_FOREST_PATH_BASE_LOCAL_ROWS_V1:',1)[1].split('= [',1)[1].split('];',1)[0]
assert re.findall(r'\[(\d+), (\d+), (\d+), (\d+)\]',table)==[('1','5','9','13')]*6
differences=[
 dict(change='schedule validation is erased from the owned reference only after its complete success law',laws=['PV_B3P_ScheduleResult133.forest_success'],accepted_packet='structural133.json; inherited V229 closed packet'),
 dict(change='forest path helper loop becomes a bounded existential and local residue predicate; all Options succeed',laws=['PV_B3P_MaskShape132.base_bounds','PV_B3P_MaskPath132.used_iff'],accepted_packet='helper formula/Option law also in inherited PV_B3P_StructuralLemmas133.forest_aux_option'),
 dict(change='legacy auxiliary translation and XOR value cells become the final local used predicate',laws=['PV_B3P_MaskSource132.legacy_bounds','PV_B3P_MaskSource132.legacy_path_absent','PV_B3P_MaskSource132.translated_value','PV_B3P_MaskSource132.native_free']),
 dict(change='Boolean source predicate is interpreted by the emitted free function',laws=['PV_B3P_MaskFreeLaw132.free_eq']),
 dict(change='Vec append becomes indexed fixed-array writes and a count; every write is retained, in order, with total capacity 3803',laws=['PV_B3P_MaskStep132.write_retained','PV_B3P_MaskPrefix132.write_prefix','PV_B3P_MaskScan132.inner','PV_B3P_MaskOuter132.outer','PV_B3P_MaskCapacity132.full_count','PV_B3P_MaskOrdered132.complete_result']),
 dict(change='machine casts and increments are interpreted without wrapping on their exact domains',laws=['PV_B3P_MaskCasts132.row','PV_B3P_MaskCasts132.column','PV_B3P_MaskLoopBounds132.row_next','PV_B3P_MaskLoopBounds132.column_next','PV_B3P_MaskLoopBounds132.count_next']),
 dict(change='array and Vec carriers retain all 3803 cells; the original op132 carrier is installed with all other fields unchanged',laws=['PV_B3P_Install132.reference','PV_B3P_Install132.value_law','PV_B3P_Install132.count_law','PV_B3P_Install132.nonvacuity'],frames=261)]
record=dict(row='V228',op=132,evidence_class='structural (K-1 substitute)',source_pin=PIN,source_revision=git('rev-parse','HEAD').decode().strip(),native_bodies=records,constants=constants,forest_local_table=[[1,5,9,13]]*6,owned_body_copy_sha256=sha(owned.encode()),reference_sha256=sha(ref.encode()),differences=differences,
 control_order='validate schedule; columns 0..16; rows 0..1024; evaluate padding/auxiliary; append one row/column cell iff free; increment row, then column; return all cells',
 error_paths='schedule succeeds under inherited closed structural packet; reference and host array never exceed capacity; all row/column casts and increments are bounded; native allocation-failure semantics are the same standing standard-library reading used by V229',
 deployed_features='features132-resume3.json: complete 435-crate deployed graph and 37-crate validation graph; reached statement/prover/core feature lists equal',
 extraction_fidelity='raw emitted Array.update value is threaded through both loops; complete_result proves retained ordered result; reference source contains no cfg/cfg! or debug_assert selection and is byte-identical to extracted source',
 finite_validation='native132-resume3-exact: unit input, statement/owned/host/reference complete ordered values; finite validation only',
 trusted_items_added=[],universal_native_machine_equality_claimed=False,row_closed=False)
if '--finalize' in sys.argv:
 resolution=json.loads((D/'structural132-project-resolution-resume3.json').read_text());receipts=[]
 for f in (D/'receipts-resume3').glob('lean-*/receipt/receipt.json'):
  rr=json.loads(f.read_text());rr['_file']=str(f.relative_to(R));receipts.append(rr)
 checked=[]
 for module,a in resolution['modules'].items():
  if not module.startswith('PV_B3P_'):continue
  good=[r for r in receipts if r['module']==module and r['source_sha256']==a['sha256'] and r['exit_status']==0]
  assert good,('missing accepted current proof',module)
  r=good[-1];stdout=(R/r['_file']).parent/'stdout.log';assert 'sorryAx' not in stdout.read_text(),module
  checked.append(dict(module=module,source_sha256=a['sha256'],receipt=r['_file'],axioms=r['print_axioms']))
 f=D/'receipts-resume3/native132-resume3-exact/receipt/receipt.json';native=json.loads(f.read_text());assert native['exit_status']==0 and native['swaps']==0
 ffeatures=D/'features132-resume3.json';features=json.loads(ffeatures.read_text());assert features['feature_differences']==[]
 inherited=json.loads((D/'structural133.json').read_text());assert inherited['row_closed']
 record.update(row_closed=True,checked_lean_modules=checked,native_receipt=str(f.relative_to(R)),feature_receipt=str(ffeatures.relative_to(R)),scope='selected callback/source/value requirement; privacy endpoint not established')
(D/'structural132-resume3.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(dict(row=record['row'],closed=record['row_closed'],checked_native_bodies=len(records))))
