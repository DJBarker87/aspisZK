from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
meta=json.loads((E/'PCD_NATIVE_PATCH_META.json').read_text());source=subprocess.check_output(['git','show','b936275465600469312d1f058cdc91ea2a11f3dc:'+meta['source']],text=True)
a=source.index('        if (afterstate.next_pair_index >> level)');b=source.index('\n    }',a);span=source[a:b]
frag=(E/'PCD_frontier_native.rs').read_text();frag=frag.replace('SOURCE_SPAN',span);assert span in frag
(E/'PCD_frontier_generated.rs').write_text(frag)
association={'source':meta['source'],'revision':'b936275465600469312d1f058cdc91ea2a11f3dc','function':'next_pair_forest_lane_v1','span':span,'span_sha256':sha(span),'source_contains':source.count(span),'fragment_contains':frag.count(span),'cut':'frontier comparison body at arbitrary level<20; iterator association is a separate native cut','status':'SOURCE_SEGMENT_CANDIDATE; complete native/model association and row gate still required','method_precedent':'NKV_FRAGMENT_ASSOCIATION under ruling ay(3); no whole-buffer unwind'}
a=source.index('    Ok(PoolV1PairForestLaneStateV1 {',source.index('fn next_pair_forest_lane_v1('));b=source.index('\n}',a);tail=source[a:b]
finish=(E/'PCD_finish_native.rs').read_text().replace('TAIL_SPAN',tail)
(E/'PCD_finish_generated.rs').write_text(finish)
guard='lane.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index)'
assert guard in source
guardFragment=(E/'PCD_guard_native.rs').read_text().replace('GUARD_EXPR','        '+guard)
(E/'PCD_guard_generated.rs').write_text(guardFragment)
association={'spans':[association,dict(source=meta['source'],revision=association['revision'],function=association['function'],span=tail,span_sha256=sha(tail),source_contains=source.count(tail),fragment_contains=finish.count(tail),cut='post-loop record return; arbitrary original lane/result; scalar observer tag/key_byte/level/word covers every returned field',status='SOURCE_SEGMENT_CANDIDATE')], 'status':'Native source segments; no whole-row certificate yet'}
association['spans'].append(dict(source=meta['source'],revision=association['spans'][0]['revision'],function='next_pair_forest_lane_v1',span=guard,span_sha256=sha(guard),source_contains=source.count(guard),fragment_contains=guardFragment.count(guard),cut='complete checked-add guard at arbitrary old/next; no success premise',status='SOURCE_SEGMENT_CANDIDATE'))
(E/'PCD_FRAGMENT_ASSOCIATION.json').write_text(json.dumps(association,indent=1)+'\n')
base=(E/'PCD_lane_native.rs').read_text();base=base.replace('    #[kani::proof_for_contract(super::next_pair_forest_lane_v1)]','    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]\n    #[kani::proof_for_contract(super::next_pair_forest_lane_v1)]').replace('    #[kani::proof]\n    fn PCD_checked_rejection_control','    #[kani::stub(core::ptr::copy_nonoverlapping, kmx::KMX_copy_nonoverlapping)]\n    #[kani::proof]\n    fn PCD_checked_rejection_control')
kmx='    mod kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
meta['annotation']=meta['annotation'].replace('Err(PoolV1ProgramError::StateHistoryMismatch.into())','Err(ProgramError::Custom(0x41532003))')
meta['root_annotation']='#![cfg_attr(kani, feature(allocator_api))]\n'
meta['suffix']='\n#[cfg(kani)]\n#[allow(non_snake_case)]\nmod PCD_harness {\n    use super::*;\n'+kmx+base+frag+finish+guardFragment+(E/'PCD_iterator_native.rs').read_text()+(E/'PCD_fidelity_native.rs').read_text()+(E/'PCD_request_reference.rs').read_text()+(E/'PCD_request_native.rs').read_text()+(E/'PCD_box_native.rs').read_text()+(E/'PCD_decode_tail_native.rs').read_text()+(E/'PCD_result_box_fidelity.rs').read_text()+'\n}\n'
meta['request_annotation']='''#[cfg_attr(kani, kani::ensures(|out| {
    let tag:u8=kani::any(); let i:usize=kani::any(); let j:usize=kani::any();
    tag>=14 || i>=8 || j>=32 || PCD_harness::PCD_request_exact(out,instruction_data,tag,i,j)
}))]
#[cfg_attr(kani, kani::modifies())]
'''
start=source.index('fn next_pair_forest_lane_v1(');modified=source[:start]+meta['annotation']+source[start:]
request_start=modified.index('fn decode_terminal_request_box_v1(')
modified=modified[:request_start]+meta['request_annotation']+modified[request_start:]+meta['suffix'];meta['modified_sha256']=sha(modified)
(E/'PCD_NATIVE_PATCH_META.json').write_text(json.dumps(meta,indent=1)+'\n');(E/'PCD_native_packets.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),modified.splitlines(True),fromfile='a/'+meta['source'],tofile='b/'+meta['source'])))
rootpath='programs/aspis-pool/src/lib.rs';root=subprocess.check_output(['git','show','b936275465600469312d1f058cdc91ea2a11f3dc:'+rootpath],text=True)
rootmodified=meta['root_annotation']+root
with (E/'PCD_native_packets.patch').open('a') as out:out.write(''.join(difflib.unified_diff(root.splitlines(True),rootmodified.splitlines(True),fromfile='a/'+rootpath,tofile='b/'+rootpath)))
p=E/'PCD_NATIVE_REPAIR_FILES.json';f=json.loads(p.read_text());f['PCD_src/programs/aspis-pool/src/lib.rs']=rootmodified;f['PCD_src/'+meta['source']]=modified;f['PCD_NATIVE_PATCH_META.json']=json.dumps(meta,indent=1)+'\n';f['PCD_FRAGMENT_ASSOCIATION.json']=(E/'PCD_FRAGMENT_ASSOCIATION.json').read_text();p.write_text(json.dumps(f,indent=1)+'\n')
print('PCD arbitrary-level native loop fragment prepared with exact frozen-span hashes and KMX stubs; not a row root.')
