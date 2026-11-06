from pathlib import Path
import json,hashlib,lzma,base64,re
B=Path(__file__).resolve().parent;payload=json.loads(lzma.decompress((B/'NKA_FROZEN_PAYLOAD.json.xz').read_bytes()));S=B/'NKA_src';sha=lambda b:hashlib.sha256(b).hexdigest();norm=lambda s:re.sub(r'\s+','',s)
original=lambda name:base64.b64decode(payload[name]).decode()
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';source=original(n);s=norm(source)
assert 'out.as_mut_ptr().cast::<[QM31;29]>().add(p).write(record.decode_k::<29>(p*29)?);' in s
assert 'forpin0..3' in s
body=(B/'NKA_write_event.rs.txt').read_text();event=norm(body)
assert 'unsafe{out.as_mut_ptr().cast::<Row>().add(p).write(reply?);}*written=true;Ok(())' in event
assert 'assert_eq!(written,success)' in event and 'letmutwritten=false' in event
q='crates/aspis-core/src/r0_transcript.rs';query=norm(original(q));assert 'letmutscan=QueryScan::default();letmutstate=advances[7];forkin0..8{ifscan.scan(&blocks[k]){state=advances[k];break;}}Ok((scan.finish()?,state))' in query
h='crates/aspis-core/src/r0/heap.rs';heap=norm(original(h));assert 'out.try_reserve_exact(1).map_err(|_|Error::Allocation)?;' in heap
assert 'out.set_len(1)' in heap and 'Box::into_raw(out.into_boxed_slice())as*mutMaybeUninit<T>' in heap
reference=norm((B/'NKA_REFERENCE_INPUT.rs.txt').read_text());assert all(x in reference for x in ['decode_k::<29>(0)?','decode_k::<29>(29)?','decode_k::<29>(58)?','heap::filled(1,value)','.into_boxed_slice()'])
run=norm((B/'NKA_generated/NKA_ClaimsReference.lean').read_text().split('def run ',1)[1].split('theorem emitted_success',1)[0]);assert run.count('reserveFilledreservation')==1
positions=[run.index(x) for x in ['decode_k29#usizevr0#usize','decode_k29#usizevr29#usize','decode_k29#usizevr58#usize','reserveFilledreservation']];assert positions==sorted(positions)
assert sha((S/'Cargo.lock').read_bytes())=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
report=dict(status='PASS',frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_pins={name:sha(original(name).encode()) for name in [n,q,h]},write_event_harness_sha256=sha(body.encode()),ghost_erasure='remove written parameter/assignment; explicit SAME decoder reply substitutes at its source boundary; typed store text identical',reference_input_sha256=sha((B/'NKA_REFERENCE_INPUT.rs.txt').read_bytes()),reference_order=positions,query_default='QueryScan derived zero default; never IncrementalMerkleTree',allocation_site='heap.uninit try_reserve_exact(1),1392bytes align4 by actual native layout assertions',domain_policy='P6 reviewed source-site association, not proof of allocator internals or initializedness from bit equality',cargo_target_dir=str(B/'NKA_target'))
(B/'NKA_SOURCE_ASSOCIATION.json').write_text(json.dumps(report,indent=2));print('NKA frozen source/cut erasure, typed-write event and original reference-site/order association PASS')
