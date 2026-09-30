#!/usr/bin/env python3
"""Replay the finite literal source/table boundary; not a Rust refinement proof."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PINS = '26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6'
EX = 'docs/research/v8-no-work-100-20260907/experiments/'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit():
    manifest = ROOT / 'evidence/r117-native-engine/r117-primal/r18-stage.json'
    assert sha(manifest) == PINS
    pins = json.loads(manifest.read_text())['files']
    sources = {}

    def source(name):
        h = pins[EX + name]
        matches = list((ROOT / 'evidence').glob('*/blobs/' + h))
        assert matches, name
        assert all(sha(path) == h for path in matches)
        sources[EX + name] = h
        return matches[0].read_text()

    rust = source('r16_basis_transport.rs')
    table = source('r17_basis_tables.rs')
    assert 'let base=|j:usize|(j&1)|(((j>>1)&63)<<4)|(((j>>7)^7)<<1);' in rust
    assert 'order.swap(127,1023);\n        order.swap(126,1021);' in rust
    order = json.loads(re.search(r'pub const ORDER: \[usize; 1024\] = (\[[^;]+\]);', table)[1])
    inactive = json.loads(re.search(r'pub const INACTIVE: \[bool; 1024\] = (\[[^;]+\]);', table)[1])
    assert len(order) == len(inactive) == 1024
    assert sorted(order) == list(range(1024))
    base = [(j & 1) | (((j >> 1) & 63) << 4) | (((j >> 7) ^ 7) << 1) for j in range(1024)]
    digit = [j % 2 + 16 * ((j // 2) % 64) + 2 * (7 - j // 128) for j in range(1024)]
    assert base == digit
    back = [r % 2 + 2 * (r // 16) + 128 * (7 - (r // 2) % 8) for r in range(1024)]
    assert all(back[base[j]] == j and base[back[j]] == j for j in range(1024))
    base[127], base[1023] = base[1023], base[127]
    one_swap = base.copy()
    base[126], base[1021] = base[1021], base[126]
    assert base == order and order[1023] == 1023 and inactive[1023]
    assert [order[j] for j in [126, 127, 1021, 1023]] == [993, 1009, 1022, 1023]
    assert all(order[j] == 16 * (j // 2) + 14 + j % 2 and inactive[order[j]] for j in range(89))

    lean = ROOT / 'lean/AspisV8R19'
    inventory = lean / 'T163SourceTable.lean'
    old = inventory.read_text()
    blocks = json.loads(re.search(r'def inactiveBlocks : List \(List Bool\) := (\[.*\])', old)[1])
    assert len(blocks) == 32 and all(len(b) == 32 for b in blocks)
    assert [x for block in blocks for x in block] == inactive
    new = lean / 'TwoSwapSourceTable.lean'
    s = new.read_text()
    for anchor in [
        'j%2+16*((j/2)%64)+2*(7-j/128)',
        'r%2+2*(r/16)+128*(7-(r/2)%8)',
        '(Equiv.swap 127 1023).trans ((Equiv.swap 126 1021).trans base)',
        'abbrev isInactive := T163SourceTable.isInactive',
        'abbrev inactive := T163SourceTable.inactive',
    ]:
        assert anchor in s
    witness = lean / 'TwoSwapWitnessData.lean'
    s = witness.read_text()
    low_order = json.loads(re.search(r'def orderValue .*?:= \((\[.*?\]) : List Nat\)', s)[1])
    low_inactive = json.loads(re.search(r'def inactiveValue .*?:= \((\[.*?\]) : List Bool\)', s)[1])
    assert low_order == order[:131]
    assert low_inactive == [inactive[r] for r in order[:131]]

    # Explicit wrong-profile controls: neither old ordering is accepted.
    old_blocks = json.loads(re.search(r'def forwardBlocks .*?:= (\[.*\])', old)[1])
    old_order = [x for b in old_blocks for x in b][:479] + list(range(479, 1024))
    one_swap_mismatches = sum(a != b for a, b in zip(one_swap, order))
    old_mismatches = sum(a != b for a, b in zip(old_order, order))
    assert one_swap_mismatches == 2 and old_mismatches > 0
    return {
        'status': 'PASS_SCOPED',
        'source_base_revision': '1cf29982431cc456ec7d0b670b6c221366e557b4',
        'selected_native_manifest_sha256': PINS,
        'source_files': sources,
        'lean_files': {str(p.relative_to(ROOT)): sha(p) for p in [inventory, new, witness]},
        'all_order_entries': 1024, 'all_inverse_entries': 1024,
        'unchanged_inactive_entries': 1024, 'first_pad_images': 89,
        'low_order_and_inactive_entries': 131,
        'one_swap_negative_mismatches': one_swap_mismatches,
        'old_t163_negative_mismatches': old_mismatches,
        'rust_word_refinement_proved': False,
        'universal_joint_coverage_proved': False,
        'full_privacy_proved': False, 'full_soundness_proved': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--record', action='store_true')
    args = parser.parse_args()
    result = audit()
    if args.record:
        output = ROOT / 'evidence/r121-two-swap-source/source-table-audit.json'
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
