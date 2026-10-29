"""Assemble explicit source/model associations; never restore by record counts."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
lib={x['relative']:x for x in json.load(open(E/'library-sources.json'))}
old=json.load(open(R/'evidence/pv-rdcd3-20261028/range-source-result.json'))
reuse=[]
for row in old['records']:
 relative=row['path'].split('/library/core/src/')[1]
 assert lib[relative]['sha256']==row['file_sha256'],relative
 reuse.append(dict(relative=relative,source_sha256=row['file_sha256'],law=row['law'],source_body=row['source_body'],original_check='evidence/pv-rdcd3-20261028/range-source-result.json',status='unchanged whole-file identity verified; fresh private Lean helper required'))
# Recover exactly the original checker output, never a renamed pin/projection tool.
gate=R/'evidence/pv-rdcd-20261028/original-gates-recovered/results.json';g=json.load(open(gate));entry=next(x for x in g['results'] if 'V201' in x['rows']);assert entry['result']=='PASS',entry
shape_key=next(k for k in g['outputs'] if k.endswith('encoder-native-shapes.json'))
shape=json.loads(g['outputs'][shape_key]);app={x['path']:x for x in json.load(open(E/'application-sources.json'))}
for row in shape['native_shapes']:assert app[row['path']]['sha256']==row['source_sha256'],row
owned_path=shape['owned_source']['path'];owned=subprocess.check_output(['git','show','HEAD:'+owned_path],cwd=R)
assert hashlib.sha256(owned).hexdigest()==shape['owned_source']['sha256']
model=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_OwnedEncoder.lean';text=model.read_text()
assert not re.search(r'let\s*\([^\n]*,\s*_\s*\)',text)
assert 'Array.update out i t1' in text
assert 'owned.basis_fill aspis_corer0scalarCodeFieldInst a width i factor' in text
assert 'owned.basis_round aspis_corer0scalarCodeFieldInst out1 i t2' in text
associations=[
 dict(source='chunks_exact(2), ChunksExact.new/next and split_at_checked',models=['PV_RDCD4_ChunkCtor194.binding','PV_RDCD4_ChunkMemory194.binding','PV_RDCD4_MemorySplit194.checked_binding','PV_RDCD4_Chunks194.message_new/next_pair/next_empty'],effects='Retain both spans, store v only on Some, retain rem and constant chunk_size2. Pointer origin/offset/length are retained by MemorySplit194.aliases/valid_parts.'),
 dict(source='array IntoIterator, PolymorphicIter.next, IndexRange.next/len/next_unchecked',models=['PV_RDCD4_ArrayIter194.new_valid/next_active/next_done','PV_RDCD4_ArrayMemory194.binding','PV_RDCD4_ArraySuffix.active/done/increment_bound','PV_RDCD4_Wrappers194.restore/through_binding/through_complete'],effects='Fully initialized Copy storage is moved into alive[0,512), start increments BEFORE the initialized read, changed alive/data return through both mutable wrappers. No dropped backward function.'),
 dict(source='const_ptr.read, ptr.read, raw slice/metadata/offset wrappers',models=['PV_RDCD4_Memory194.read_forward/read_at/read_frame','PV_RDCD4_Memory194.raw_parts_forward/metadata_forward/raw_parts_fields','PV_RDCD4_MemorySplit194.left_values/right_values/partition/aliases/valid_parts'],effects='Same typed source region and exact element offset/length. Legal pointer/read preconditions follow the typed input and live-range/split invariants; no arbitrary invalid-pointer claim. Intrinsic typed-memory/layout execution stays V370.'),
 dict(source='Iterator.zip -> Zip.new -> NoCoerce general-default macro; Iterator.into_iter; Option map/and_then/Try',models=['PV_RDCD4_Zip194.first_none/second_none/both_some','PV_RDCD4_Option194.map_binding/and_then_binding/residual_none','PV_RDCD4_EncoderNext.empty/pair','PV_RDCD4_EncoderRefinement.source'],effects='Sequential a.next before b.next. First None leaves b unchanged; second None retains advanced a. index/len fields remain zero/unused. Exactly512 entered iterations plus final exhausted inspection; every original callback Result outcome retained.'),
 dict(source='Copy/drop glue on iterator, elements, references and closure captures',models=['PV_RDCD4_ArrayIter194.drop_copy'],effects='Concrete WideExact satisfies CodeField:Copy, so Rust Copy coherence forbids a user Drop. IntoIter.drop needs_drop<WideExact> is false; ManuallyDrop suppresses automatic inner drop. ChunksExact contains borrowed slices and usize only. Compiler type/drop semantics remain V370; no arbitrary destructor law.'),
 dict(source='basis.values, double, range/index/write loops and eval_pair/eval_message',models=['PV_DL_EncoderBasis.half_rank/native_min/advance_val/source/basis_source','PV_DL_EncoderFill.source','PV_DL_EncoderBounds.cells/target_val/writes','PV_DL_EncoderMutation.restoration','PV_RDCD3_RangeLoop.complete/all_endpoints','PV_RDCD3_Index194.array_complete/slice_complete','PV_RDCD3_ArrayWrite194.complete/read_back/frame','PV_RDCD4_EncoderEntries.run_bridge/iteration','PV_RDCD4_V201.source_reference'],effects='Original four complete application bodies and six explicit source/reference differences are reused at unchanged hashes. All basis writes return changed arrays; field callbacks are the original complete CodeField Result boundary, never a new abstract library callback.'),
]
required=['PV_RDCD4_ChunkCtor194','PV_RDCD4_V201_R073','PV_RDCD4_V201_R109','PV_RDCD4_V201_R110','PV_RDCD4_V201_R134','PV_RDCD4_V201_R136','PV_RDCD4_V201_R137','PV_RDCD4_Double194','PV_RDCD4_V201_R138','PV_RDCD4_V201_R139']
receipts=[]
for p in E.glob('lean-*/receipt.json'):
 j=json.load(open(p))
 if j.get('exit')==0:receipts.append(j)
passed={j['module'].split('/')[-1] for j in receipts};pending=[x for x in required if x not in passed]
out=dict(row='V201',source_associations=associations,range_reuse=reuse,original_checker=dict(path=str(gate.relative_to(R)),sha256=hashlib.sha256(gate.read_bytes()).hexdigest(),result=entry,application_shape_key=shape_key,application_shapes=shape['native_shapes'],owned_source=shape['owned_source'],differences=shape['differences']),d188=dict(model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),checks=['basis_cell returns Array.update','basis_fill passes changed a','basis_round passes changed out1','no tuple-discarded backward function'],native='native-v201-wide/receipt.json; finite validation, including inherited changed-write witness'),pending_new_modules=pending,scope='Source/Result at original CodeField parameter boundary only. Not a standalone native producer, full world/state-on-crash or observer theorem.',before='Complete deployed concrete source-to-owned-reference Result law was an open library-transport obligation.',after='Same inputs, quantifiers, CodeField boundary and Result carrier. Kernel source_reference passes; source closure restoration remains pending any listed modules plus final coherent source/object checks.',compiler='V370/D381/D386 retained',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],T='entropy_law, entropy_kernel, observation; unchanged')
(E/'v201-proof-association.json').write_text(json.dumps(out,indent=2)+'\n');print('Exact original checker reuse and8 unchanged range/index bodies verified; pending modules:',pending)
