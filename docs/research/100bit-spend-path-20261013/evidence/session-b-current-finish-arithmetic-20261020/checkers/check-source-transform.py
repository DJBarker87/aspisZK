from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
raw_funs = (root/'generated/Funs.lean').read_text()
raw_types = (root/'generated/Types.lean').read_text()
proof = (root/'sources/CurrentWideEqSemanticV7.lean').read_text()
retained_types = (root/'sources/retained-current-Types.lean').read_text()
def drop_resource_options(s):
    return '\n'.join(line for line in s.splitlines()
        if not (line.strip().startswith('set_option maxHeartbeats ') or
                line.strip().startswith('set_option maxRecDepth ')))+'\n'
clean_funs = drop_resource_options(raw_funs)
clean_types = drop_resource_options(raw_types)
assert clean_types == retained_types, 'resource-cleaned generated Types differ from retained current Types'
assert proof.startswith(clean_funs+'\nnamespace AspisR1CurrentWide\n'), 'proof source is not exact generated Funs plus appended theorems'
assert 'set_option maxHeartbeats' not in proof and 'set_option maxRecDepth' not in proof
assert 'def field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq' in raw_funs
assert 'if b' in raw_funs[raw_funs.index('def field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq'):]
assert (root/'sources/rust-input/lib.rs').read_text().endswith(
    'pub fn wide_eq_entry(x: field::WideExact, y: field::WideExact) -> bool { x == y }\n')
manifest = {
 'raw_generated_funs_sha256': sha(root/'generated/Funs.lean'),
 'raw_generated_types_sha256': sha(root/'generated/Types.lean'),
 'retained_current_types_sha256': sha(root/'sources/retained-current-Types.lean'),
 'accepted_lean_source_sha256': sha(root/'sources/CurrentWideEqSemanticV7.lean'),
 'rust_wrapper_source_sha256': sha(root/'sources/rust-input/lib.rs'),
 'resource_option_transform': 'remove exactly lines beginning with set_option maxHeartbeats or set_option maxRecDepth; all remaining generated Funs is the prefix of accepted proof source; resource-cleaned generated Types is byte-identical to retained current Types source',
 'result': 'PASS'
}
(root/'source-transform-check.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps(manifest, indent=2))
