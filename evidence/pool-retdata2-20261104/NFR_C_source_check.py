"""Strict source-cut/feature check; source inspection, never a native certificate."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
read=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
p='programs/aspis-pool/src/pair_forest.rs';s=read(p)
manifest=json.loads((E/'NFR_C_SOURCE_CUT.json').read_text());assert hashlib.sha256(s.encode()).hexdigest()==manifest['source_sha256']
helper=manifest['encoder_helper'];assert helper in s
expected='''#[inline(never)]
fn terminal_result_bytes_box_v1(
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES]>, ProgramError> {
    Ok(Box::new(
        encode_pool_v1_pair_forest_terminal_result_v1(result)
            .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?,
    ))
}

'''
assert helper==expected
cut=manifest['settlement_cut'];assert cut in s
assert cut.count('let result = authenticated.value();')==1
assert cut.count('        result,')==2 # mutually exclusive validation branches
assert cut.count('next_lane_image_box_v1(&lane, result)?')==1
assert cut.count('terminal_result_bytes_box_v1(result)?')==1
assert cut.count('authenticated.exact_bytes()')==1
cpi=s[s.index('    let authenticated = verify('):s.index('    let result = authenticated.value();')]
assert cpi.rstrip().endswith(')?;')
assert cpi.count('verify(')==1
assert 'get_return_data' not in cut and 'invoke' not in cut and 'set_return_data' not in cut
features=json.loads((E/'NFR_K001-metadata-pin.json').read_text())['features_all_crates']
f=next(x['features'] for x in features if x['name']=='aspis-pool')
assert {'r1-split-checkpoint','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit'}<=set(f)
assert 'pair-forest-direct-result-audit' not in f
assert 'pair-forest-verifier-lane-invariant-audit' in f
result=dict(frozen_revision=REV,source=p,source_sha256=manifest['source_sha256'],helper_literal_exact=True,post_verify_getter_direct=True,three_same_reference_uses=True,no_runtime_read_in_cut=True,exact_bytes_shortcut_enabled=False,feature_receipt='NFR_K001-metadata-pin.json',classification='static source/feature association only; no CFG/extraction or native process credit')
(E/'NFR_C_SOURCE_CHECK.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
