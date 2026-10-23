from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2k-20261023';P=E/'S2K-native/src'
src=(R/'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs').read_text()
items=[('magic',0,4,'output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);','POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]',None),('version',4,5,'output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;','POOL_V1_PAIR_FOREST_TERMINAL_VERSION',None),('kind',5,6,'output[5] = result.transition_kind as u8;','if withdrawal {2} else {1}',None),('digest_version',6,7,'output[6] = POOL_V1_DIGEST_ENCODING_VERSION;','POOL_V1_DIGEST_ENCODING_VERSION',None),('lane',7,8,'output[7] = result.output_lane;','result.output_lane',None),('master',8,40,'output[RESULT_MASTER_OFFSET..RESULT_SELECTED_LANE_OFFSET]\n        .copy_from_slice(&result.master_account);','result.master_account[j]','S2K_copy32'),('selected',40,72,'output[RESULT_SELECTED_LANE_OFFSET..RESULT_NULLIFIER_OFFSET]\n        .copy_from_slice(&result.selected_lane_account);','result.selected_lane_account[j]','S2K_copy32'),('nullifier',72,104,'output[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]\n        .copy_from_slice(&encode_digest_canonical(&result.nullifier));','(result.nullifier[j/4].0 >> (8*(j%4))) as u8','S2K_copy32'),('afterstate',104,792,'output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(\n        &encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)\n            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?,\n    );','source[j]','S2K_copy688')]
out='// Exact result-encoder field boundaries. Sub-encoder output and errors\n// are separate obligations; these gates do not assume emit success.\n';cuts={}
for name,start,end,cut,expected,callee in items:
 assert cut in src
 attr=f'#[kani::stub_verified({callee})]\n' if callee else ''
 body=cut
 for a,b in [('RESULT_MASTER_OFFSET','8'),('RESULT_SELECTED_LANE_OFFSET','40'),('RESULT_NULLIFIER_OFFSET','72'),('RESULT_AFTERSTATE_OFFSET','104')]:body=body.replace(a,b)
 if callee:
  source={'master':'result.master_account','selected':'result.selected_lane_account','nullifier':'encode_digest_canonical(&result.nullifier)','afterstate':'kani::any::<[u8;688]>()'}[name]
  body=f'let source={source};\n    {callee}(&mut output[{start}..{end}],&source,j,source[j]);'
 out+=f'''#[kani::proof]
#[kani::unwind(34)]
{attr}fn S2K_result_field_{name}() {{
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {{
      transition_kind:if withdrawal {{PoolV1TransitionKind::Withdrawal}} else {{PoolV1TransitionKind::PrivateTransfer}},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {{next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}}
    }};
    let j:usize=kani::any(); kani::assume(j<{end-start});
    let i:usize=kani::any(); kani::assume(i<792 && (i<{start} || i>={end}));
    let before=output[i];
    {body}
    assert_eq!(output[{start}+j],{expected});
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j=={end-start-1});
}}
'''
 cuts[name]=dict(source='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs',source_sha256=hashlib.sha256(src.encode()).hexdigest(),cut=cut,range=[start,end],callee=callee,afterstate_note='arbitrary sub-encoder output bytes; status and encoding relation separate' if name=='afterstate' else None)
(P/'S2K_result_fields.rs').write_text(out);(E/'result-field-cuts.json').write_text(json.dumps(cuts,indent=2)+'\n')
p=P/'lib.rs';s=p.read_text();line='include!("S2K_result_fields.rs");\n';assert line not in s;p.write_text(s+'\n'+line)
