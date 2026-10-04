#!/usr/bin/env python3
"""Generate source-pinned guarded point-1 transport leaf lemmas only."""
from __future__ import annotations
import argparse, hashlib, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.r21-scratch/r753-point1-basis-generator/guarded-chunks'
PLAN = ROOT / '.r21-scratch/r748-chosen222-point1-leaf-plan.json'
PINNED = {
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/T163SourceTable.lean': '6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/TwoSwapSourceTable.lean': '88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R746SelectedJointMinor.lean': 'f2f1623052e035a0d9a8d6e635df38a9cfd3ee7177b84255a1f7065ea60ee399',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/IndexSchedule.lean': '363b0eb4491d3cb40ad5d097e5e7f0242677f43808a1839bafe80add2356cfcf',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748JointWitnessPointEntry.lean': '06dafa57a87f421dff2014f34f5f809cebf2cd418958e582b137451a43fe7276',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R750WitnessPointSupport.lean': 'cc7736c8fa2948f1a351a7b1626f5cadf88b9ff92c1e1b8db9b57ab443c17e4a',
    'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R752SharedWitnessPointSupport.lean': '67e79e1b6ef6b65b92633aa0625deb5a87def5ccd29e8be6890db8165034ef55',
    '.r21-scratch/R754Point1GuardedTransport.lean': 'f7af56ed8c49709ed749747f26f5d955b4e89ea1487f36043125f5dcdee3e7d0',
    '.r21-scratch/r748-chosen222-point1-leaf-plan.json': '55f19bf194589ef1229ae6d96ce0d7ef16b1b8d3466b40d00cc0e9fa4b906dd4',
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def source_inputs() -> dict[str, bytes]:
    return {p: (ROOT / p).read_bytes() for p in PINNED}

def render_leaf(leaf: int, original: int, inactive: bool) -> str:
    guard = f'''  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
'''
    member = f'''  have hmem : ({original} : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change ({original} : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change ({original} : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
'''
    nonmember = f'''  have hmem : ({original} : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change ({original} : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : ({original} : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change ({original} : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive ({original} : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive ({original} : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
'''
    value = 576 if inactive else 0
    branch = '  simp only [if_pos hmem] at hw\n' if inactive else '  simp only [if_neg hmem] at hw\n'
    return f'''lemma w_guarded_leaf_{leaf:04d} :
    R748JointWitnessPointEntry.w {leaf} = ({value} : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨{leaf}, by omega⟩
  have ho : order j = ({original} : Fin 1024) := by decide
{guard}{member if inactive else nonmember}  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
{branch}  simpa [j] using hw

#print axioms w_guarded_leaf_{leaf:04d}
'''

def render_chunks(leaves: list[dict]) -> dict[str, bytes]:
    chunks: dict[str, bytes] = {}
    for base in range(0, len(leaves), 32):
        group = leaves[base:base+32]
        idx = base // 32
        header = '''import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R754Point1GuardedTransport
import AspisV8R19.R752SharedWitnessPointSupport
import AspisV8R19.T163SourceTable
import AspisV8R19.TwoSwapSourceTable

namespace AspisR19.R754Point1GuardedLeaves
open AspisV8R16 AspisV8R17 AspisV8R19 AspisR19
open AspisR19.TwoSwapSourceTable
set_option maxRecDepth 4096
noncomputable section

'''
        body = ''.join(render_leaf(x['leaf'], x['original'], x['inactive']) for x in group)
        footer = f'''end
end AspisR19.R754Point1GuardedLeaves
'''
        chunks[f'Point1GuardedChunk{idx:02d}.lean'] = (header + body + footer).encode()
    return chunks

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    inp = source_inputs()
    for path, expected in PINNED.items():
        actual = sha(inp[path])
        if actual != expected:
            raise SystemExit(f'PIN MISMATCH {path}: expected {expected}, got {actual}')
    plan = json.loads(inp['.r21-scratch/r748-chosen222-point1-leaf-plan.json'])
    recs = plan['leaf_records']
    guard = [x for x in recs if x['basis_zero_by_p01']]
    assert len(guard) == 323
    existing = set(map(int, re.findall(r'^lemma w_(\d+)', inp['docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748JointWitnessPointEntry.lean'].decode(), re.M)))
    leaves = [x for x in guard if x['leaf'] not in existing]
    assert len(leaves) == 303
    outputs = render_chunks(leaves)
    manifest = {
        'scope': 'R754 guarded point-1 transport leaves generated from exact 323 plan records, skipping the 20 named R748 w_i leaves',
        'source_sha256': {p: sha(b) for p,b in inp.items()},
        'guarded_plan_leaf_count': len(guard),
        'preexisting_r748_leaf_count_skipped': len(guard)-len(leaves),
        'new_leaf_count': len(leaves),
        'chunk_limit': 32,
        'outputs_sha256': {n: sha(b) for n,b in outputs.items()},
        'leaf_indices': [x['leaf'] for x in leaves],
    }
    manifest_bytes = (json.dumps(manifest, indent=2)+'\n').encode()
    if args.check:
        if not OUT.is_dir():
            raise SystemExit(f'missing output directory {OUT}')
        expected_names = set(outputs) | {'manifest.json'}
        actual_names = {p.name for p in OUT.iterdir() if p.is_file()}
        if actual_names != expected_names:
            raise SystemExit(f'OUTPUT SET MISMATCH missing={sorted(expected_names-actual_names)} extra={sorted(actual_names-expected_names)}')
        for name, body in outputs.items():
            actual=(OUT/name).read_bytes()
            if actual != body:
                raise SystemExit(f'OUTPUT MISMATCH {name}: expected {sha(body)} got {sha(actual)}')
        if (OUT/'manifest.json').read_bytes() != manifest_bytes:
            raise SystemExit('manifest mismatch')
        print(f'PASS inputs=8 guarded=323 skipped=20 generated=303 chunks={len(outputs)} each<=32')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, body in outputs.items():
            (OUT/name).write_bytes(body)
        (OUT/'manifest.json').write_bytes(manifest_bytes)
        print(f'WROTE {OUT} generated=303 chunks={len(outputs)}')
        for name, body in outputs.items():
            print(f'{name} sha256={sha(body)} bytes={len(body)}')
    return 0

if __name__ == '__main__':
    sys.exit(main())
