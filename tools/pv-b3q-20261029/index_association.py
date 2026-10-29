from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3q-20261029');x=json.loads((D/'deployed-index-sources.json').read_text());rows=[]
plans={
('core/src/array/mod.rs','as_slice'):('PV_B3Q_ArrayView.unsizing_link',['borrow self unchanged','unsize array reference to slice using same base and constant length','no store; shared lifetime preserved; intrinsic pointer realization V370']),
('core/src/array/mod.rs','as_mut_slice'):('PV_B3Q_ArrayView.unsizing_link',['borrow self exclusively','unsize array reference to mutable slice using same base and constant length','the length invariant is retained in Restorer; restoring applies the list update to original fixed array','no allocation or destructor; pointer realization V370']),
('core/src/array/mod.rs','index'):('PV_B3Q_ArrayView.read_binding',['unsize self to slice','delegate to slice Index for usize','source bounds check and arrayOutOfBounds result retained; unwinding/failure-event association remains separate']),
('core/src/array/mod.rs','index_mut'):('PV_B3Q_ArrayBorrow.mutable_link',['unsize self to mutable slice','delegate to slice IndexMut for usize','return loan and restore original fixed array after applying returned slice back function','no returned back function is dropped']),
('core/src/slice/index.rs','index'):('PV_B3Q_ArrayView.read_binding',['slice Index wrapper delegates index.index(self)','usize SliceIndex uses intrinsic indexing (*slice)[self]','check index below slice length, return same element or bounds panic','model read branch represents bounds failure; source panic effects not proved by value equality']),
('core/src/slice/index.rs','index_mut'):('PV_B3Q_ArrayBorrow.slice_borrow_projection',['slice IndexMut wrapper delegates index.index_mut(self)','usize SliceIndex uses intrinsic indexing &mut (*slice)[self]','check index below length, return loan of exact slot','logical restoration is Slice.set; complete success/fail/div model tags retained; native panic effects remain separate']),
('core/src/slice/mod.rs','len'):('PV_B3Q_ArrayView.view_length',['read slice pointer metadata length','no element read or write','return metadata as usize; pointer metadata intrinsic V370']),
('core/src/iter/adapters/enumerate.rs','new'):('PV_B3Q_Iterator4.iterator_links',['move inner iterator into iter field','initialize count=0','no drop/abort/allocation']),
('core/src/iter/adapters/enumerate.rs','next'):('PV_B3Q_Iterator4.enumerate_binding',['call inner.next before touching count','None returns None via ? and leaves count unchanged','Some saves count, increments it with release wrapping semantics, returns (old_count,item)','on actual four-slot constructor count=index; increment cannot overflow by IteratorAlignment','no element mutation; returned mutable loan is preserved']),
('core/src/slice/iter/macros.rs','next'):('PV_B3Q_Iterator4.next_binding',['cache old ptr and end_or_len','for actual QM31, size=16 and IS_ZST=false; unreachable ZST branch omitted only for this specialization','compare ptr to end with same allocation provenance; empty returns None without advancing','otherwise self.ptr=ptr.add(1) within original four-slot slice','return old ptr as mutable reference only after advancing; no element write or destructor','logical region+index port proves end-test and index-increment; memory intrinsics remain V370'])}
for record in x['rows']:
 for item in record['items']:
  key=(record['file'],item['name'])
  if key not in plans:continue
  # Restrict overloaded Index and iterator items to actual source bodies discussed.
  text=item['text']
  if key[0]=='core/src/slice/index.rs' and not ('index.index' in text or '(*slice)[self]' in text):continue
  if key[0]=='core/src/iter/adapters/enumerate.rs' and item['line']not in[23,79]:continue
  if key[0]=='core/src/slice/iter/macros.rs' and item['line']!=157:continue
  lemma,steps=plans[key]
  rows.append(dict(file=record['file'],source_file_sha256=record['file_sha256'],line=item['line'],source_item_sha256=item['sha256'],source_item=text,lemma=lemma,steps=steps,evidence_class='structural own-1 for described specialization; proof status requires successful matching source receipt',existing_link='PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14',compiler_boundary='V370 / D381,D386 retained'))
(D/'index-source-association.json').write_text(json.dumps(dict(rows=rows,complete_cone=False,unclosed=['all omitted generic/specialized alternatives require actual reachability classification','bounds-panic effects and unwind/abort association','complete pointer/dependency body catalogue']),indent=2)+'\n');print(len(rows))
