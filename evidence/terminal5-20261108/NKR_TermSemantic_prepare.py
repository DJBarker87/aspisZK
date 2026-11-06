from pathlib import Path
import subprocess,json,hashlib,difflib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
s=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_TermSemantic_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;d=1
 while d:d+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
b=body(s,'semantic_packed');prefix=b[b.index('let mut packed'):b.index('#[cfg(not(feature = "pool-v1-pair-forest-packed-digest-audit"))]')]
expected='''let mut packed = [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
add_schedule_lanes(&mut packed, public, openings, selectors);
add_path_lanes(&mut packed, openings, selectors);
add_value_lanes(&mut packed, openings, selectors);
add_occupancy_lanes(&mut packed, public, openings, selectors);'''
assert compact(prefix)==compact(expected),'Frozen prefix changed'
for n,args in [('schedule','packed,public,openings,selectors,l'),('path','packed,openings,selectors,l'),('value','packed,openings,selectors,l'),('occupancy','packed,public,openings,selectors,l')]:assert 'NKR_sem_'+n+'('+args+')' in compact(body(code,'NKR_semantic_child_window'))
digest='''let digests = public_digest_packed(public, openings, selectors);
packed[84 / 4] = packed[84 / 4].add(digests[0]);
packed[84 / 4 + 1] = packed[84 / 4 + 1].add(digests[1]);'''
assert compact(digest) in compact(b),'Frozen digest window changed'
translated='''let digests=NKR_sem_digest(public,openings,selectors,l);
packed[84/4]=NKR_sem_add(packed[84/4],digests[0],l);
packed[84/4+1]=NKR_sem_add(packed[84/4+1],digests[1],l);'''
assert compact(body(code,'NKR_semantic_digest_window'))==compact(translated)
scalar=b[b.index('let asset_difference'):];expectedScalar='''let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
let private_transfer_term = selectors.row(28 * 16 + 12).mul(asset_difference);
let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
let withdrawal_term = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2).mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
let scalars = scalar_lanes(public.variant,public.withdrawal_amount.is_some(),input_asset,output_scalar,private_transfer_term,withdrawal_term,);
add_preweighted(&mut packed, 92, &scalars);
packed'''
assert compact(scalar)==compact(expectedScalar),'Frozen scalar expression/control changed'
translatedScalar='''let asset_difference=NKR_sem_sub(openings.z[1],NKR_sem_lift(public.asset_id,l),l);
let input_asset=NKR_sem_mul(NKR_sem_row(selectors,2*16+12,l),asset_difference,l);
let output_scalar=NKR_sem_mul(NKR_sem_row(selectors,31*16+12,l),asset_difference,l);
let private_transfer_term=NKR_sem_mul(NKR_sem_row(selectors,28*16+12,l),asset_difference,l);
let withdrawal_amount_value=public.withdrawal_amount.unwrap_or(0);
let withdrawal_term=NKR_sem_mul(NKR_sem_row(selectors,16*VALUE_AUXILIARY_BLOCK+2,l),NKR_sem_sub(openings.z[10],NKR_sem_lift(M31(withdrawal_amount_value),l),l),l);
let scalars=NKR_sem_scalars(public.variant,public.withdrawal_amount.is_some(),input_asset,output_scalar,private_transfer_term,withdrawal_term,l);
NKR_sem_scalar_pack(packed,92,&scalars,l);'''
assert compact(body(code,'NKR_semantic_scalar_window'))==compact(translatedScalar)
name='crates/aspis-statement/src/pool_v1/NKR_TermSemantic_native.rs';new=s+'\n#[cfg(kani)]\n#[path="NKR_TermSemantic_native.rs"]\nmod NKR_semantic_native;\n'
patch=''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));(E/'NKR_TermSemantic_native.patch').write_text(patch)
(E/'NKR_TermSemantic_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),prefix=prefix,order=[232,229,233,228],digest=digest,translated_digest=translated,scalar=scalar,translated_scalar=translatedScalar,identity=True,native_shapes=['NKR_semantic_child_cut','NKR_semantic_zero_cut','NKR_semantic_order_cut','NKR_semantic_digest_cut','NKR_semantic_scalar_cut'],scope='One actual full24child boundary at arbitraryprestate; literal4callcontrol; one2write digestwindow; final14call scalar/preweighted92window. No field multiplication evaluated.'),indent=2))
print('Semantic261 frozen windows and operand expression trees PASS')
