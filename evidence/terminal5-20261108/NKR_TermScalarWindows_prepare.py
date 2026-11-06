from pathlib import Path
import subprocess,json,hashlib,difflib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_TermScalarWindows_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;d=1
 while d:d+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
b=body(old,'semantic_packed');frozen=b[b.index('let asset_difference'):]
expected='''let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
let private_transfer_term = selectors.row(28 * 16 + 12).mul(asset_difference);
let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
let withdrawal_term = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2).mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
let scalars = scalar_lanes(public.variant,public.withdrawal_amount.is_some(),input_asset,output_scalar,private_transfer_term,withdrawal_term,);
add_preweighted(&mut packed,92,&scalars);packed'''
assert compact(frozen)==compact(expected),'Frozen scalar expression/control changed'
expressions=['NKR_swindow_lift(asset,l)','NKR_swindow_sub(opened[1],locals[0],l)','NKR_swindow_row(selectors,2*16+12,l)','NKR_swindow_mul(locals[2],locals[1],l)','NKR_swindow_row(selectors,31*16+12,l)','NKR_swindow_mul(locals[4],locals[1],l)','NKR_swindow_row(selectors,28*16+12,l)','NKR_swindow_mul(locals[6],locals[1],l)','NKR_swindow_row(selectors,16*VALUE_AUXILIARY_BLOCK+2,l)','NKR_swindow_lift(M31(withdrawal_amount.unwrap_or(0)),l)','NKR_swindow_sub(opened[10],locals[9],l)','NKR_swindow_mul(locals[8],locals[10],l)']
for k,x in enumerate(expressions):assert str(k)+'=>'+x in compact(body(code,'NKR_scalar_field_window'))
assert 'locals[stage]=next;' in compact(body(code,'NKR_scalar_field_window'))
tail='''let scalars=NKR_swindow_scalars(variant,withdrawal_amount.is_some(),products[0],products[1],products[2],products[3],l);NKR_swindow_preweighted(packed,92,&scalars,l);'''
assert compact(body(code,'NKR_scalar_tail_window'))==compact(tail)
name='crates/aspis-statement/src/pool_v1/NKR_TermScalarWindows_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_TermScalarWindows_native.rs"]\nmod NKR_scalar_windows_native;\n';patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source));patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));(E/'NKR_TermScalarWindows_native.patch').write_text(patch)
(E/'NKR_TermScalarWindows_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),frozen=frozen,stages=expressions,locals_mapping=['liftAsset','difference','row44','inputAsset','row508','outputScalar','row460','privateTransfer','row1010','liftAmount','withdrawalDifference','withdrawalTerm'],tail=tail,identity=True,retired='K05614callwindow TIMEOUT, never rerun',scope='One arbitrary native field/row statement on12value prestate +pointwise fullframe; separate258/23092suffix with complete2/24replies. No field product evaluated.'),indent=2))
print('261 scalar isolated field/tail frozen windows PASS')
