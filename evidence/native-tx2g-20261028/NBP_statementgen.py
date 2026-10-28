from pathlib import Path
import sys
sys.dont_write_bytecode=True
from NBP_patch_sources import added_patch,pieces
import subprocess,difflib
E=Path(__file__).resolve().parent
# Pure, unrolled natural byte spelling for the closed digest serializer.
s='''use super::*;
fn NBP_digest_bytes(d:&aspis_core::hash::Digest)->[u8;32] {
'''
# Digest location verify imported Digest alias from module; use generic explicit field type path below.
s=s.replace('aspis_core::hash::Digest','Digest')
for i in range(8):s+=f' let b{i}=d[{i}].0.to_le_bytes();\n'
s+=' ['+','.join(f'b{i}[{j}]' for i in range(8) for j in range(4))+']\n}\n'
s+='''#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(crate::atomic_statement::encode_digest_canonical, NBP_digest_bytes)]
fn NBP_common_encoder() {
 let mut out:[u8;216]=kani::any();let before=out;
 let magic:[u8;4]=kani::any();let withdrawal:bool=kani::any();
 let kind=if withdrawal{PoolV1TransitionKind::Withdrawal}else{PoolV1TransitionKind::PrivateTransfer};
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NBP_digest(),nullifier:NBP_digest(),asset_id:M31(kani::any())};
 let j:usize=kani::any();kani::assume(j<216);
 super::encode_common(&mut out,magic,kind,c);
 let expected=match j {
 0..=3=>magic[j],4=>1,5=>if withdrawal{2}else{1},6=>1,7=>before[j],
 8..=39=>c.pool[j-8],40..=71=>c.deployment_domain[j-40],
 72..=79=>c.anchor_sequence.to_le_bytes()[j-72],
 80..=111=>NBP_digest_bytes(&c.anchor_root)[j-80],
 112..=143=>NBP_digest_bytes(&c.nullifier)[j-112],
 144..=147=>c.asset_id.0.to_le_bytes()[j-144],_=>before[j]};
 assert!(out[j]==expected);kani::cover!(j==215);
}
fn NBP_digest()->Digest { [M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())] }
'''
# One generic native copy body at each common component range, arbitrary pre-state.
for name,start,width in [('magic',0,4),('pool',8,32),('deployment',40,32),('sequence',72,8),('anchor',80,32),('nullifier',112,32),('asset',144,4),('recipient',152,32),('change',184,32),('amount',148,4),('destination',152,32)]:
 s+=f'''#[kani::proof]
#[kani::unwind(256)]
fn NBP_store_{name}() {{
 let mut out:[u8;216]=kani::any();let before=out;let src:[u8;{width}]=kani::any();
 let j:usize=kani::any();kani::assume(j<216);
 out[{start}..{start+width}].copy_from_slice(&src);
 assert!(out[j]==if j>={start}&&j<{start+width}{{src[j-{start}]}}else{{before[j]}});
 kani::cover!(j=={start+width-1});
}}
'''
p='crates/aspis-statement/src/pool_v1/payment_relation.rs';old=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);new=old+'\n#[cfg(kani)]\nmod NBP_codecs;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/payment_relation/NBP_codecs.rs'))
(E/'NBP_statement.patch').write_text(patch)
# Native decoder association, each coordinate as well as complete error result.
old=s
s+='''fn NBP_raw32(b:&[u8;216],off:usize)->[u8;32] {
'''+ ' ['+','.join(f'b[off+{i}]' for i in range(32))+']\n}\n'
s+='''fn NBP_common_spec(b:&[u8;216])->Result<CommonPublicV1,PoolV1PaymentStatementFormatError> {
 let asset=u32::from_le_bytes([b[144],b[145],b[146],b[147]]);
 if asset>=P {return Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId);}
 let root=crate::atomic_statement::decode_digest_canonical(&NBP_raw32(b,80)).map_err(|_|PoolV1PaymentStatementFormatError::NonCanonicalDigest)?;
 let nullifier=crate::atomic_statement::decode_digest_canonical(&NBP_raw32(b,112)).map_err(|_|PoolV1PaymentStatementFormatError::NonCanonicalDigest)?;
 let c=CommonPublicV1{pool:NBP_raw32(b,8),deployment_domain:NBP_raw32(b,40),anchor_sequence:u64::from_le_bytes([b[72],b[73],b[74],b[75],b[76],b[77],b[78],b[79]]),anchor_root:root,nullifier,asset_id:M31(asset)};
 super::validate_common(c)?;Ok(c)
}
#[kani::proof]
#[kani::unwind(256)]
fn NBP_common_decoder() {
 let b:[u8;216]=kani::any();let j:usize=kani::any();kani::assume(j<32);
 match (super::decode_common(&b),NBP_common_spec(&b)) {
 (Err(a),Err(e))=>assert!(a==e),
 (Ok(a),Ok(c))=>{assert!(a.pool[j]==c.pool[j]);assert!(a.deployment_domain[j]==c.deployment_domain[j]);assert!(a.anchor_sequence==c.anchor_sequence);assert!(a.anchor_root[j%8]==c.anchor_root[j%8]);assert!(a.nullifier[j%8]==c.nullifier[j%8]);assert!(a.asset_id==c.asset_id);},
 _=>assert!(false),
 }
 kani::cover!(b[144]==255);
}
'''
p='crates/aspis-statement/src/pool_v1/payment_relation/NBP_codecs.rs'
(E/'NBP_statement2.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
