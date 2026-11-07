from pathlib import Path
import hashlib,json,lzma,base64,difflib
B=Path.cwd();S=B/'NMX_src';p=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
p=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
# The module is already installed; only own Kani instrumentation changes.
(S/'programs/r1-cost-probe/src/NMX_217_iteration.rs').write_bytes((B/'NMX_217_iteration.rs').read_bytes())
payload0=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()))
field=S/'crates/aspis-core/src/field.rs';original=base64.b64decode(payload0['crates/aspis-core/src/field.rs'])
suffix=b'\n#[cfg(kani)] #[path="NMX_217_arbitrary.rs"] mod NMX_217_arbitrary;\n'
assert field.read_bytes() in [original,original+suffix]
field.write_bytes(original+suffix)
(S/'crates/aspis-core/src/NMX_217_arbitrary.rs').write_bytes((B/'NMX_217_arbitrary.rs').read_bytes())
# Mechanical source-cut validation, before compiling any native gate.
import re
norm=lambda x:re.sub(r'\s+','',x)
full=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()))
frozen=base64.b64decode(full['programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode()
original=frozen[frozen.index('        *node = decode_digest_canonical('):]
original=original[:original.index('        if (next_leaf_index')]
arg='tree[start..start+32].try_into().map_err(|_|ProgramError::InvalidAccountData)?'
expected=norm(original).replace(arg,'window')
helper=(B/'NMX_217_iteration.rs').read_text()
actual=helper[helper.index('    *node = decode_digest_canonical('):]
actual=actual[:actual.index('    Ok(())')]
assert norm(actual)==expected,('assignment source cut drift',norm(actual),expected)
guard=frozen[frozen.index('        if (next_leaf_index >> level)'):]
guard=guard[guard.index('if ')+3:guard.index(' {')]
actual_guard=helper[helper.index('    (next_leaf_index >> level)'):]
actual_guard=actual_guard[:actual_guard.index('\n}')]
assert norm(actual_guard)==norm(guard),'guard source cut drift'
assert 'ifmaster==[0u8;32]' in norm(frozen)
assert 'fnNMX_master_zero(master:&[u8;32])->bool{*master==[0u8;32]}' in norm(helper)
prefix=frozen[frozen.index('    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES'):]
prefix=prefix[:prefix.index('    let root = decode_digest_canonical(')]
actual=helper[helper.index(' let actual:Result<NMX_prefix_state,ProgramError>=(||{')+len(' let actual:Result<NMX_prefix_state,ProgramError>=(||{'):]
actual=actual[:actual.index('    let root_window:')]
assert norm(actual)==norm(prefix).replace('bytes.len()','logical_len'),'entry-to-child prefix source drift'
final=frozen[frozen.index('    if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]'):]
final=final[:final.index('\n}')]
actual=helper[helper.index(' let actual:Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>=(||{')+len(' let actual:Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>=(||{'):]
actual=actual[:actual.index(' })();')]
assert norm(actual)==norm(final).replace('bytes[72]','bump').replace('bytes[5]','lane_id'),'post-loop-to-return source drift'
assert 'bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES].iter().any(|byte|*byte!=0)' in norm(frozen)
assert 'fnNMX_reserved(bytes:&[u8;7])->bool{bytes.iter().any(|byte|*byte!=0)}' in norm(helper)
constructor=frozen[frozen.index('    Ok(Box::new(PoolV1PairForestLaneStateV1 {'):]
constructor=constructor[:constructor.index('\n}')].replace('Ok(Box::new','Box::new',1)[:-1]
constructor=constructor.replace('bytes[72]','input.bump').replace('bytes[5]','input.lane_id').replace('        master,','        master: input.master,').replace('            next_leaf_index,','            next_leaf_index: input.tree.next_leaf_index,').replace('            root,','            root: input.tree.root,').replace('            frontier,','            frontier: input.tree.frontier,')
actual=helper[helper.index(' let output =')+len(' let output ='):]
actual=actual[:actual.index(';\n *output')]
assert norm(actual)==norm(constructor),'constructor field/source drift'
payload=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()));diffs=[]
for rel in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','crates/aspis-core/src/field.rs']:
 original=base64.b64decode(payload[rel]).decode();diffs.extend(difflib.unified_diff(original.splitlines(True),(S/rel).read_text().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
for name in ['NMX_217_native.rs','NMX_217_reference.rs','NMX_217_fidelity.rs','NMX_217_iteration.rs']:
 rel='programs/r1-cost-probe/src/'+name;diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
rel='crates/aspis-core/src/NMX_217_arbitrary.rs';diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
(B/'NMX_217_harness.patch').write_text(''.join(diffs));print('Prepared source-ordered one-iteration contracts; actual decoder body unchanged')
