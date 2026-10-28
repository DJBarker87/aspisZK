# Additional isolated source windows; no enclosing codec is replaced by success.
header_jobs=[
 ('pair_terminal.rs','decode_pool_v1_pair_verified_afterstate_v1','    let next_root',688,'ASJA','PoolV1PairVerifierTransportErrorV1','NBH_after',[("bytes[4]!=1",'WrongVersion'),('bytes[5]!=1','WrongPairFormat'),('bytes[6]!=1','WrongDigestEncoding'),('bytes[7]!=1','WrongSuccessCode')]),
 ('pair_forest_terminal.rs','decode_pool_v1_pair_forest_terminal_request_v1','    let public',320,'ASQ8','PoolV1PairForestTerminalFormatErrorV1','NBH_terminal',[("bytes[4]!=1",'WrongVersion'),('bytes[5]!=1 && bytes[5]!=2','InvalidTransitionKind'),('bytes[6]!=1','WrongDigestEncoding'),('bytes[7]!=0','NonZeroBinding')]),
 ('pair_forest_accounts.rs','decode_pool_v1_pair_forest_master_v1','    if bytes[50..64]',384,'ASM8','PoolV1PairForestAccountErrorV1','NBH_accounts',[("bytes[4]!=2",'WrongVersion'),('bytes[5]!=8','WrongLaneCount'),('bytes[6]!=1','WrongDigestEncoding')]),
 ('pair_forest_accounts.rs','decode_pool_v1_pair_forest_checkpoint_v1','    if bytes[176..]',192,'ASC8','PoolV1PairForestAccountErrorV1','NBH_accounts',[("bytes[4]!=2",'WrongVersion'),('bytes[5]!=8','WrongLaneCount'),('bytes[6]!=1','WrongDigestEncoding')])]
for f,name,stop,N,magic,err,child,checks in header_jobs:
 src=body(f,name);prefix=src[:src.index(stop)]
 checks=[(f'bytes.len()!={N}','WrongLength'),(f'&bytes[..4]!=b"{magic}"','WrongMagic')]+checks
 expr=' else '.join('if '+c+' {Err('+err+'::'+e+')}' for c,e in checks)+' else {Ok(())}'
 p=ROOT+child+'.rs'
 if p not in files:files[p]='use super::*;\n'
 short=magic.lower()
 files[p]+=f'''fn NBH_{short}_header(bytes: &[u8])->Result<(),{err}> {{{prefix} Ok(())}}
#[kani::proof]
fn NBH_{short}_header_gate() {{let raw:[u8;{N+1}]=kani::any();let n:usize=kani::any();kani::assume(n<={N+1});let bytes=&raw[..n];assert_eq!(NBH_{short}_header(bytes),{expr});}}
'''
 probes[short+'_header']={'source_prefix':prefix,'sha256':hashlib.sha256(prefix.encode()).hexdigest(),'scope':'pending suffix, not codec success; arbitrary bounded slice; no loops'}
# Store ONE iteration at arbitrary offset, arbitrary output and arbitrary child bytes.
for f,name,child,N,offset in [('pair_terminal.rs','encode_pool_v1_pair_verified_afterstate_v1','NBH_after',688,48),('pair_tree_profile.rs','encode_pool_v1_pair_live_snapshot_v1','NBH_live',800,160)]:
 src=body(f,name);loop=src[src.index('    for (level, node)'):src.index('    Ok(output)' if N==688 else '    Ok(())')]
 inner=loop[loop.index('{')+1:loop.rindex('}')]
 assert inner.count('encode_digest_canonical(node)')==1
 native=inner.replace('&encode_digest_canonical(node)','&bytes')
 files[ROOT+child+'.rs']+=f'''fn NBH_store{N}(output: &mut [u8;{N}], level:usize,bytes:[u8;32]) {{{native}}}
#[kani::proof]
fn NBH_store{N}_gate() {{let mut out:[u8;{N}]=kani::any();let old=out;let bytes:[u8;32]=kani::any();let level:usize=kani::any();kani::assume(level<20);let j:usize=kani::any();kani::assume(j<{N});NBH_store{N}(&mut out,level,bytes);let start={offset}+32*level;assert_eq!(out[j],if j>=start && j<start+32 {{bytes[j-start]}} else {{old[j]}});}}
'''
 probes[f'store{N}']={'source_loop':loop,'iteration':inner,'transformation':'one arbitrary enumerate iteration, child encode_digest result explicit bytes parameter; lower digest encoder dependency remains OPEN','domain':f'level<20, all output[{N}] and bytes[32] arbitrary; proves complete byte frame using arbitrary j'}
# Late preflight is checked before all output mutation and child calls.
src=body('pair_tree_profile.rs','encode_pool_v1_pair_late_public_statement_v1');prefix=src[:src.index('    output.fill')]
prefix=prefix.replace('statement.live_snapshot.next_pair_index','before').replace('statement.candidate_afterstate.next_pair_index','after')
files[ROOT+'NBH_live.rs']+=f'''fn NBH_late_preflight(before:u64,after:u64,output:&mut[u8])->Result<(),PoolV1PairLatePublicStatementErrorV1>{{{prefix} Ok(())}}
#[kani::proof]
fn NBH_late_preflight_gate() {{let before:u64=kani::any();let after:u64=kani::any();let mut out:[u8;1521]=kani::any();let old=out;let n:usize=kani::any();kani::assume(n<=1521);let got=NBH_late_preflight(before,after,&mut out[..n]);let expected=if n!=1520 {{Err(PoolV1PairLatePublicStatementErrorV1::WrongLength)}}else if before==u64::MAX || after!=before.wrapping_add(1) {{Err(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch)}}else{{Ok(())}};assert_eq!(got,expected);let j:usize=kani::any();kani::assume(j<1521);assert_eq!(out[j],old[j]);}}
'''
probes['late_preflight']={'source_prefix':prefix,'domain':'all u64 indices; bounded output widths including 1520; unchanged output before children'}
# Native prefix stores with arbitrary child results. Prefixes are windows in
# a future full Result composition; not calls to a fabricated successful codec.
src=body('pair_terminal.rs','encode_pool_v1_pair_verified_afterstate_v1')
s=src[src.index('    let mut output'):src.index('    for (level, node)')]
s=s.replace('afterstate.next_pair_index','index').replace('&encode_digest_canonical(&afterstate.next_root)','&root')
files[ROOT+'NBH_after.rs']+=f'''fn NBH_asja_stores(index:u64,root:[u8;32])->[u8;688]{{{s}output}}
#[kani::proof]
fn NBH_asja_stores_gate(){{let index:u64=kani::any();let root:[u8;32]=kani::any();let out=NBH_asja_stores(index,root);let j:usize=kani::any();kani::assume(j<688);let header=[65,83,74,65,1,1,1,1];let expected=if j<8{{header[j]}}else if j<16{{index.to_le_bytes()[j-8]}}else if j<48{{root[j-16]}}else{{0}};assert_eq!(out[j],expected);}}
'''
probes['asja_stores']={'source_window':s,'scope':'validation precedes this window; root result parameter retains OPEN lower encode dependency'}
src=body('pair_tree_profile.rs','encode_pool_v1_pair_live_snapshot_v1')
s=src[src.index('    output.fill'):src.index('    for (level, node)')]
s=s.replace('snapshot.pool','pool').replace('snapshot.deployment_domain','domain').replace('snapshot.sequence','seq').replace('snapshot.next_pair_index','index').replace('&encode_digest_canonical(&snapshot.current_root)','&root')
files[ROOT+'NBH_live.rs']+=f'''fn NBH_live_stores(output:&mut[u8;800],pool:[u8;32],domain:[u8;32],seq:u64,index:u64,root:[u8;32]){{{s}}}
#[kani::proof]
fn NBH_live_stores_gate(){{let mut out:[u8;800]=kani::any();let pool:[u8;32]=kani::any();let domain:[u8;32]=kani::any();let seq:u64=kani::any();let index:u64=kani::any();let root:[u8;32]=kani::any();NBH_live_stores(&mut out,pool,domain,seq,index,root);let j:usize=kani::any();kani::assume(j<800);let expected=if j<8{{b"ASPLIVE1"[j]}}else if j==8{{1}}else if j<16{{0}}else if j<48{{POOL_V1_PAIR_TREE_FORMAT_BINDING[j-16]}}else if j<80{{pool[j-48]}}else if j<112{{domain[j-80]}}else if j<120{{seq.to_le_bytes()[j-112]}}else if j<128{{index.to_le_bytes()[j-120]}}else if j<160{{root[j-128]}}else{{0}};assert_eq!(out[j],expected);}}
'''
probes['live_stores']={'source_window':s,'scope':'length/validation precede this window; arbitrary initial output; explicit root child result; domain at80..112'}
# ASF8 first: arbitrary already projected statement fields. Root bytes are an
# explicit child result, not an assumption of a valid statement.
src=body('pair_forest_terminal.rs','encode_pool_v1_pair_forest_terminal_statement_v1')
s=src[src.index('    let mut output'):src.index('    encode_pool_v1_pair_late_public_statement_v1(')]
s=s.replace('statement.transition_kind() as u8','kind').replace('common.output_lane','lane').replace('common.master_account','master').replace('common.checkpoint_account','checkpoint').replace('common.selected_lane_account','selected').replace('common.checkpoint_sequence','seq').replace('&encode_digest_canonical(&common.historical_global_anchor)','&anchor')
files[ROOT+'NBH_terminal.rs']+=f'''fn NBH_asf8_stores(kind:u8,lane:u8,master:[u8;32],checkpoint:[u8;32],selected:[u8;32],seq:u64,anchor:[u8;32])->[u8;1880]{{{s}output}}
#[kani::proof]
fn NBH_asf8_stores_gate(){{let kind:u8=kani::any();let lane:u8=kani::any();let master:[u8;32]=kani::any();let checkpoint:[u8;32]=kani::any();let selected:[u8;32]=kani::any();let seq:u64=kani::any();let anchor:[u8;32]=kani::any();let out=NBH_asf8_stores(kind,lane,master,checkpoint,selected,seq,anchor);let j:usize=kani::any();kani::assume(j<1880);let expected=if j<4{{b"ASF8"[j]}}else if j==4{{1}}else if j==5{{kind}}else if j==6{{1}}else if j==7{{lane}}else if j<40{{master[j-8]}}else if j<72{{checkpoint[j-40]}}else if j<104{{selected[j-72]}}else if j<112{{seq.to_le_bytes()[j-104]}}else if j<144{{anchor[j-112]}}else{{0}};assert_eq!(out[j],expected);}}
'''
probes['asf8_stores']={'source_window':s,'scope':'prefix before late/payment calls; exact accounts and ordered field offsets; validation/projections/child digest dependencies explicit'}
# ASR8 deliberately last: it has no headline soundness need (op53 universal).
src=body('pair_forest_terminal.rs','encode_pool_v1_pair_forest_terminal_result_v1')
s=src[src.index('    let mut output'):src.index('    output[RESULT_AFTERSTATE_OFFSET..]')]
s=s.replace('result.transition_kind as u8','kind').replace('result.output_lane','lane').replace('result.master_account','master').replace('result.selected_lane_account','selected').replace('&encode_digest_canonical(&result.nullifier)','&nullifier')
files[ROOT+'NBH_terminal.rs']+=f'''fn NBH_asr8_stores(kind:u8,lane:u8,master:[u8;32],selected:[u8;32],nullifier:[u8;32])->[u8;792]{{{s}output}}
#[kani::proof]
fn NBH_asr8_stores_gate(){{let kind:u8=kani::any();let lane:u8=kani::any();let master:[u8;32]=kani::any();let selected:[u8;32]=kani::any();let nullifier:[u8;32]=kani::any();let out=NBH_asr8_stores(kind,lane,master,selected,nullifier);let j:usize=kani::any();kani::assume(j<792);let expected=if j<4{{b"ASR8"[j]}}else if j==4{{1}}else if j==5{{kind}}else if j==6{{1}}else if j==7{{lane}}else if j<40{{master[j-8]}}else if j<72{{selected[j-40]}}else if j<104{{nullifier[j-72]}}else{{0}};assert_eq!(out[j],expected);}}
'''
probes['asr8_stores']={'source_window':s,'scope':'non-headline emission prefix only; full encoder OPEN'}
