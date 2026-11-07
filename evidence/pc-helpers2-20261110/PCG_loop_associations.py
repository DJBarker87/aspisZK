from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows={x['row']:x for x in json.loads((E/'PCG_SOURCE_MAP.json').read_text())}
s=rows['POOL:293']['body'];n=lambda s:re.sub(r'\s+','',s)
expected='''{let mut seed=[0u8;POOL_V1_PAIR_FOREST_MARKER_SEED_BYTES];let mut chunk=0;while chunk<4{let mut word=0u64;let mut byte=0;while byte<7{word=(word<<8)|u64::from(digest[7*chunk+byte]);byte+=1;}let mut group=0;while group<8{seed[8*chunk+group]=((word>>(7*(7-group)))&0x7f)as u8;group+=1;}chunk+=1;}seed}'''
assert n(s)==n(expected),'changed source loop skeleton'
assert 'pub const POOL_V1_PAIR_FOREST_MARKER_SEED_BYTES: usize = 32;' in (E/'PCG_nullifier.rs.txt').read_text()
assert 'fn word_association' in (E/'PCG_293.rs').read_text()
assert 'fn write_window' in (E/'PCG_293.rs').read_text()
assert 'fn group_association' in (E/'PCG_293.rs').read_text()
r=dict(row='POOL:293',body_sha256=rows['POOL:293']['frozen_body_sha256'],exact_source_loop=True,
 native_steps={'word':'PCG_293::word_association K076/K077','write':'PCG_293::write_window K078/K079','group':'PCG_293::group_association K080/K081'},
 invariants=['chunk<4','byte<7; word<256^byte; read index7*chunk+byte<28','group<8; offset8*chunk+group<32; all other positions unchanged','all loop counters increase by1 and stay <=8'],
 lean_associations=['PCG_PackLaw.read_suffix','PCG_PackComposition.chunk_word','PCG_PackComposition.chunk_group','PCG_PackComposition.pack_at','PCG_PackComposition.writeRange_exact','PCG_PackComposition.chunk_induction','PCG_PackComposition.row_293'],
 trust='P6/D188 native contract semantic transport and reviewed source transcription; reclassification, not removal')
(E/'PCG_LOOP_ASSOCIATION.json').write_text(json.dumps(r,indent=1)+'\n');print('Frozen packing loop skeleton and three native step associations recorded')
