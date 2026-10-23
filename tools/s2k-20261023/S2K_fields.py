from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]; E=R/'docs/research/100bit-spend-path-20261013/evidence/s2k-20261023'; P=E/'S2K-native/src'
src=(R/'crates/aspis-statement/src/pool_v1/pair_terminal.rs').read_text()
fields=[('magic','output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);',0,4,'POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC[j]'),('transport','output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;',4,5,'POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION'),('storage','output[5] = super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;',5,6,'POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION'),('digest_version','output[6] = POOL_V1_DIGEST_ENCODING_VERSION;',6,7,'POOL_V1_DIGEST_ENCODING_VERSION'),('success','output[7] = 1;',7,8,'1'),('index','output[8..16].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());',8,16,'afterstate.next_pair_index.to_le_bytes()[j]'),('root','output[16..48].copy_from_slice(&encode_digest_canonical(&afterstate.next_root));',16,48,'(afterstate.next_root[j/4].0 >> (8*(j%4))) as u8')]
out='// Individual source field writes; arbitrary complete original buffer.\n'
manifest={}
for name,cut,start,end,expected in fields:
 assert cut in src
 body=cut.replace('super::','')
 attr=''
 if name=='root':
  body='let source=encode_digest_canonical(&afterstate.next_root);\n    S2K_copy32(&mut output[16..48],&source,j,source[j]);'
  attr='#[kani::stub_verified(S2K_copy32)]\n'
 out+=f'''#[kani::proof]
#[kani::unwind(34)]
{attr}fn S2K_field_{name}() {{
    let mut output:[u8;688]=kani::any();
    let afterstate=PoolV1PairVerifiedAfterstateV1 {{ next_pair_index:kani::any(), next_root:digest(), next_frontier:[[M31(0);8];20] }};
    let j:usize=kani::any(); kani::assume(j<{end-start});
    let i:usize=kani::any(); kani::assume(i<688 && (i<{start} || i>={end}));
    let before=output[i];
    {body}
    assert_eq!(output[{start}+j],{expected});
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j=={end-start-1});
}}
'''
 manifest[name]={'source':'crates/aspis-statement/src/pool_v1/pair_terminal.rs','source_sha256':hashlib.sha256(src.encode()).hexdigest(),'cut':cut,'range':[start,end],'replacement':'verified S2K_copy32' if name=='root' else 'super path qualified by existing wildcard import'}
(P/'S2K_fields.rs').write_text(out)
(E/'field-cuts.json').write_text(json.dumps(manifest,indent=2)+'\n')
p=P/'lib.rs';s=p.read_text();line='include!("S2K_fields.rs");\n';assert line not in s;p.write_text(s+'\n'+line)
