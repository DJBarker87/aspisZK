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
payload=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()));diffs=[]
for rel in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','crates/aspis-core/src/field.rs']:
 original=base64.b64decode(payload[rel]).decode();diffs.extend(difflib.unified_diff(original.splitlines(True),(S/rel).read_text().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
for name in ['NMX_217_native.rs','NMX_217_reference.rs','NMX_217_fidelity.rs','NMX_217_iteration.rs']:
 rel='programs/r1-cost-probe/src/'+name;diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
rel='crates/aspis-core/src/NMX_217_arbitrary.rs';diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
(B/'NMX_217_harness.patch').write_text(''.join(diffs));print('Prepared source-ordered one-iteration contracts; actual decoder body unchanged')
