from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=E/'NJB_digest.rs.txt';s=p.read_text();s+='''
fn NJB_digest_group(opened:[QM31;16],expected:Digest,g:usize,prepared_high:PreparedQm31Multiplier,log:&mut NJB_Log)->QM31{
 let residuals=[opened[4*g].NJB_sub(lift_m31(expected[4*g]),log),opened[4*g+1].NJB_sub(lift_m31(expected[4*g+1]),log),opened[4*g+2].NJB_sub(lift_m31(expected[4*g+2]),log),opened[4*g+3].NJB_sub(lift_m31(expected[4*g+3]),log)];
 prepared_high.NJB_mul(NJB_pack(&residuals,log),log)
}
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_digest_group_proof(){let w:[[u32;4];16]=kani::any();let opened:[QM31;16]=unsafe{core::mem::transmute(w)};let expected:[M31;8]=unsafe{core::mem::transmute::<[u32;8],[M31;8]>(kani::any())};let r:[[u32;4];32]=kani::any();let cache:[[u32;3];3]=kani::any();let g:usize=kani::any();let slot:usize=kani::any();let limb:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(g<2&&slot<4&&limb<4&&row<3&&col<3);kani::assume(canon(w[4*g])&&canon(w[4*g+1])&&canon(w[4*g+2])&&canon(w[4*g+3])&&expected[4*g].0<2147483647&&expected[4*g+1].0<2147483647&&expected[4*g+2].0<2147483647&&expected[4*g+3].0<2147483647);kani::assume(canon(r[0])&&canon(r[1])&&canon(r[2])&&canon(r[3])&&canon(r[4])&&canon(r[5]));let mut l=log(r,cache);let out=NJB_digest_group(opened,expected,g,prepared_from_words(cache),&mut l);assert_eq!(l.calls,6);assert_eq!(l.kind[slot],2);assert_eq!(l.inputs[slot][limb],w[4*g+slot][limb]);assert_eq!(l.right[slot][limb],if limb==0{expected[4*g+slot].0}else{0});assert_eq!(l.kind[4],5);assert_eq!(l.lengths[4],4);assert_eq!(l.packs[4][slot][limb],r[slot][limb]);assert_eq!(l.kind[5],4);assert_eq!(l.cache_seen[5][row][col],cache[row][col]);assert_eq!(l.right[5][limb],r[4][limb]);assert_eq!(words(out)[limb],r[5][limb]^if cfg!(NJB_invert){1}else{0});}
''';p.write_text(s)
(E/'NJB_update_digest.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/NJB_digest.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_bytes((b/'NJB_digest.rs.txt').read_bytes());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('timed-out two-block shape split into one arbitrary four-lane window')
''')
x=json.loads((E/'NJB_L070.json').read_text());x.update(attempt='NJB_L073',sources=['NJB_update_digest.py','NJB_digest.rs.txt','NJB_DIGEST_ERASURE.json'],command=['python3','NJB_update_digest.py']);(E/'NJB_L073.json').write_text(json.dumps(x))
for n,inv in [(60,False),(61,True)]:
 old='NJB_K055'if inv else'NJB_K054';a=f'NJB_K{n:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[p.replace(old,a)for p in x['collect']];x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_semantic_terminal::NJB_digest_native::NJB_digest_group_proof';x['expected_time']='Split K054 timeout into arbitrary group, six logged calls, no actual multiplication';(E/(a+'.json')).write_text(json.dumps(x))
