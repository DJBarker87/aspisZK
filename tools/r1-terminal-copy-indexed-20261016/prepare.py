#!/usr/bin/env python3
"""Build an isolated candidate overlay from this worktree's pinned baseline."""
from pathlib import Path
import difflib, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
REV = 'a8930e677bc745854b9f693b5628c8a8bd2ac848'
PATHS = {
    'lib.rs': ROOT / 'crates/aspis-statement/src/lib.rs',
    'state_only_poseidon.rs': ROOT / 'crates/aspis-statement/src/state_only_poseidon.rs',
    'pool_v1/pair_forest_semantic_terminal.rs': ROOT / 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs',
}
sha = lambda b: hashlib.sha256(b).hexdigest()

def function_block(s: str, name: str):
    # Locate the Rust function body, then balance braces. The selected bodies
    # contain no brace characters in string literals/comments.
    import re
    m = re.search(r'(?m)^\s*(?:pub\s+)?(?:unsafe\s+)?fn\s+' + re.escape(name) + r'\b', s)
    if not m:
        raise ValueError(f'missing function {name}')
    start = s.find('{', m.end())
    if start < 0:
        raise ValueError(f'missing body {name}')
    depth = 0
    for j in range(start, len(s)):
        if s[j] == '{': depth += 1
        elif s[j] == '}':
            depth -= 1
            if depth == 0: return m.start(), j + 1
    raise ValueError(f'unclosed body {name}')

def edit_fn(s, name, old, new, count=1):
    a,b = function_block(s,name)
    block=s[a:b]
    if block.count(old) != count:
        raise ValueError(f'{name}: expected {count} matches for {old!r}, got {block.count(old)}')
    block=block.replace(old,new)
    return s[:a]+block+s[b:]

# Capture or reload the exact committed baseline. Re-running after overlay is safe.
old_manifest=OUT/'source-pin-manifest.json'
base={}
if old_manifest.exists():
    recorded=json.loads(old_manifest.read_text())
    if recorded.get('base_revision') != REV: raise ValueError('base revision mismatch')
    for rel,src in PATHS.items():
        raw=(OUT/'base'/rel).read_bytes()
        if sha(raw) != recorded['base_files'][rel]['sha256']: raise ValueError(f'base snapshot hash mismatch: {rel}')
        base[rel]=raw
else:
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() != REV:
        raise ValueError('worktree HEAD does not match pinned base revision')
    for rel,src in PATHS.items():
        raw=src.read_bytes(); base[rel]=raw
        git_path=src.relative_to(ROOT).as_posix()
        committed=subprocess.check_output(['git','show',f'{REV}:{git_path}'],cwd=ROOT)
        if sha(raw) != sha(committed): raise ValueError(f'working source differs from pinned commit: {git_path}')
        dst=OUT/'base'/rel; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(raw)

# Insert a source-local Copy array constructor and a row helper lift. The
# arithmetic closure remains byte-identical; row outputs use the input snapshot
# copied before any writes to state.
lib=base['lib.rs'].decode()
marker='extern crate alloc;\n'
helper='''\n\n/// Isolated Copy-array construction candidate: initialize, then call FnMut\n/// at indices 0..N in increasing order.\n#[inline(always)]\npub(crate) fn array_from_fn_copy<T: Copy, const N: usize>(\n    init: T,\n    mut f: impl FnMut(usize) -> T,\n) -> [T; N] {\n    let mut out = [init; N];\n    let mut i = 0usize;\n    while i < N {\n        out[i] = f(i);\n        i += 1;\n    }\n    out\n}\n'''
if lib.count(marker)!=1: raise ValueError('lib alloc marker mismatch')
lib=lib.replace(marker,marker+helper,1)

state=base['state_only_poseidon.rs'].decode()
oldloop='''        let mut output = 0usize;\n        while output < 4 {\n            let raw = core::array::from_fn(|limb| {\n                let a = u64::from(input[0][limb]);\n                let b = u64::from(input[1][limb]);\n                let c = u64::from(input[2][limb]);\n                let d = u64::from(input[3][limb]);\n                match output {\n                    0 => 2 * a + 3 * b + c + d,\n                    1 => a + 2 * b + 3 * c + d,\n                    2 => a + b + 2 * c + 3 * d,\n                    3 => 3 * a + b + c + 2 * d,\n                    _ => unreachable!(),\n                }\n            });\n            state[start + output] = extension_from_raw_limbs(raw);\n            output += 1;\n        }\n'''
newloop='''        state[start] = external_linear_lazy_row(input, 0);\n        state[start + 1] = external_linear_lazy_row(input, 1);\n        state[start + 2] = external_linear_lazy_row(input, 2);\n        state[start + 3] = external_linear_lazy_row(input, 3);\n'''
if state.count(oldloop)!=1: raise ValueError('current row loop mismatch')
state=state.replace(oldloop,newloop,1)
row='''
#[inline(always)]
fn external_linear_lazy_row(input: [[u32; 4]; 4], output: usize) -> QM31 {
            let raw = crate::array_from_fn_copy::<_, 4>(0u64, |limb| {
                let a = u64::from(input[0][limb]);
                let b = u64::from(input[1][limb]);
                let c = u64::from(input[2][limb]);
                let d = u64::from(input[3][limb]);
                match output {
                    0 => 2 * a + 3 * b + c + d,
                    1 => a + 2 * b + 3 * c + d,
                    2 => a + b + 2 * c + 3 * d,
                    3 => 3 * a + b + c + 2 * d,
                    _ => unreachable!(),
                }
            });
    extension_from_raw_limbs(raw)
}
'''
anchor='''\n/// Addition-only Poseidon external layer with one reduction per output limb.\n'''
if state.count(anchor)!=1: raise ValueError('external row insertion anchor mismatch')
state=state.replace(anchor,row+anchor,1)
# Scope replacements to exact named function bodies and expected multiplicity.
for fn, old, new, count in [
 ('external_linear_lazy','core::array::from_fn(|column|','crate::array_from_fn_copy::<_, 4>([0u64; 4], |column|',1),
 ('external_linear_lazy','core::array::from_fn(|limb|','crate::array_from_fn_copy::<_, 4>(0u64, |limb|',2),
 ('external_local_packed_raw','core::array::from_fn(|output|','crate::array_from_fn_copy::<_, 4>([0u64; 4], |output|',1),
 ('external_local_packed_raw','core::array::from_fn(|limb|','crate::array_from_fn_copy::<_, 4>(0u64, |limb|',1),
 ('internal_linear_lazy','core::array::from_fn(|limb|','crate::array_from_fn_copy::<_, 4>(0u64, |limb|',3),
 ('evaluate_state_only_poseidon_oracle_projected','core::array::from_fn(|group|','crate::array_from_fn_copy::<_, 4>(QM31::ZERO, |group|',1),
]:
    state=edit_fn(state,fn,old,new,count)

terminal=base['pool_v1/pair_forest_semantic_terminal.rs'].decode()
for fn, old, new, count in [
 ('add_preweighted','core::array::from_fn(|slot|','crate::array_from_fn_copy::<_, 4>(QM31::ZERO, |slot|',1),
 ('semantic_initial_and_absorption','core::array::from_fn(|lane|','crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |lane|',1),
 ('absorption_lanes_literal','core::array::from_fn(|lane|','crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |lane|',1),
 ('composition_parts','        z: core::array::from_fn(|column|','        z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column|',1),
 ('composition_parts','        succ_z: core::array::from_fn(|column|','        succ_z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column|',1),
 ('composition_parts','        xor12_z: core::array::from_fn(|column|','        xor12_z: crate::array_from_fn_copy::<_, 16>(QM31::ZERO, |column|',1),
 ('composition_parts','let mask_only = core::array::from_fn(|column|','let mask_only = crate::array_from_fn_copy::<_, 10>(QM31::ZERO, |column|',1),
 ('terminal_qm31','core::array::from_fn(|i|','crate::array_from_fn_copy::<_, 84>(QM31::ZERO, |i|',1),
]:
    terminal=edit_fn(terminal,fn,old,new,count)
# Exact fixed-length reverse-index candidate; preserves order 23..0 then 3..0.
old='''    for lane in semantic.into_iter().rev() {\n        composition = prepared_theta.mul(composition).add(lane);\n    }\n    for lane in poseidon.into_iter().rev() {\n        composition = prepared_theta.mul(composition).add(lane);\n    }\n'''
new='''    for index in (0..semantic.len()).rev() {\n        composition = prepared_theta.mul(composition).add(semantic[index]);\n    }\n    for index in (0..poseidon.len()).rev() {\n        composition = prepared_theta.mul(composition).add(poseidon[index]);\n    }\n'''
if terminal.count(old)!=1: raise ValueError('composition iterator loop mismatch')
terminal=terminal.replace(old,new,1)

candidates={'lib.rs':lib.encode(),'state_only_poseidon.rs':state.encode(),'pool_v1/pair_forest_semantic_terminal.rs':terminal.encode()}
for rel,data in candidates.items():
    dst=OUT/'candidate'/rel; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(data)
    PATHS[rel].write_bytes(data)
    (OUT/'patches'/rel.replace('/','__').replace('.rs','.patch')).parent.mkdir(parents=True,exist_ok=True)
    diff=''.join(difflib.unified_diff(base[rel].decode().splitlines(True),data.decode().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
    (OUT/'patches'/rel.replace('/','__').replace('.rs','.patch')).write_text(diff)

manifest={
 'scope':'isolated source candidate only; no build, replay, adoption, or equivalence claim',
 'base_revision':REV,
 'base_files':{rel:{'sha256':sha(base[rel]),'path':str(src.relative_to(ROOT))} for rel,src in PATHS.items()},
 'candidate_files':{rel:{'sha256':sha(candidates[rel]),'path':str((ROOT/'crates/aspis-statement/src'/rel))} for rel in PATHS},
 'transformations':{
   'lib.rs':'added local array_from_fn_copy<T:Copy,const N> helper, increasing FnMut calls after [init;N]',
   'state_only_poseidon.rs':'lifted existing external row calculation to helper with same copied input and exact arithmetic; transformed nine remaining selected production from_fn calls',
   'pool_v1/pair_forest_semantic_terminal.rs':'transformed eight selected production from_fn calls; replaced semantic/poseidon owning reverse iterators with reverse index loops'
 },
 'call_counts':{'copy_array_replacements':18,'indexed_reverse_folds':2},
 'r18_harness':{
   'path':'tools/r1-cost-probe/src/bin/r18_replay.rs',
   'sha256':sha((ROOT/'tools/r1-cost-probe/src/bin/r18_replay.rs').read_bytes()),
   'cargo_manifest_sha256':sha((ROOT/'tools/r1-cost-probe/Cargo.toml').read_bytes()),
   'cargo_lock_sha256':sha((ROOT/'Cargo.lock').read_bytes()),
   'current_source_revision':REV,
   'route':'stage1 [3,10] with 3 accounts [proof RO, public RO, verifier checkpoint W]; stage2 ASQ8 with 7 read-only nonsigner accounts'
 },
 'latest_prior_execution_evidence':{
   'terminal_validator_summary':'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-regression-20261016/SUMMARY.json',
   'terminal_validator_summary_sha256':sha((ROOT/'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-regression-20261016/SUMMARY.json').read_bytes()),
   'terminal_validator_archive':'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-regression-20261016/evidence.tar.gz',
   'terminal_validator_archive_sha256':sha((ROOT/'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-regression-20261016/evidence.tar.gz').read_bytes()),
   'r18_combined_summary':'docs/research/100bit-spend-path-20261013/evidence/r18-combined-regression-20261016/SUMMARY.json',
   'r18_combined_summary_sha256':sha((ROOT/'docs/research/100bit-spend-path-20261013/evidence/r18-combined-regression-20261016/SUMMARY.json').read_bytes()),
   'r18_combined_archive':'docs/research/100bit-spend-path-20261013/evidence/r18-combined-regression-20261016/evidence.tar.gz',
   'r18_combined_archive_sha256':sha((ROOT/'docs/research/100bit-spend-path-20261013/evidence/r18-combined-regression-20261016/evidence.tar.gz').read_bytes()),
   'interpretation':'Prior successful exact 3/7-route runs; not a measurement of this candidate.'
 },
 'fixture':{
   'proof':'docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin',
   'proof_sha256':'8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62',
   'proof_bytes':124343,
   'public':'docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin',
   'public_sha256':'72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172',
   'public_bytes':1880
 },
 'instrumentation':'compare-checkpoints.py consumes one completed r18_replay output directory and records SHA-256/byte equality for checkpoint.bin, ASR8, initial images, and stage-specific result bytes; it does not run transactions or include keys.',
 'change_inventory':{
   'from_fn_sites':[
     {'file':'crates/aspis-statement/src/state_only_poseidon.rs','functions':['external_linear_lazy_row','external_linear_lazy','external_local_packed_raw','internal_linear_lazy','evaluate_state_only_poseidon_oracle_projected'],'count':10},
     {'file':'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs','functions':['add_preweighted','semantic_initial_and_absorption','absorption_lanes_literal','composition_parts','r0::Public::terminal_qm31'],'count':8}],
   'indexed_reverse_sites':['composition_parts.semantic[23..0]','composition_parts.poseidon[3..0]'],
   'only_tracked_source_paths_changed':['crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/state_only_poseidon.rs','crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs']
 },
 'status':'source candidate prepared; all compilation/runtime cost validation pending root review'
}
(OUT/'source-pin-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files':manifest['candidate_files'],'call_counts':manifest['call_counts']},indent=2))
