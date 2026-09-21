#!/usr/bin/env python3
"""Stage the exact 1024-point cyclic-G candidate on an R38 copy.

This stager is deliberately source-pinned and diagnostic-only.  It preserves
the old 2048-point implementation as ``apply_2048_reference`` and routes the
actual caller through the supplied cyclic routine; no SBF build is performed.
"""
import argparse
import hashlib
import json
import shutil
from pathlib import Path

EXPERIMENTS = Path("docs/research/v8-no-work-100-20260907/experiments")
FAST_G = EXPERIMENTS / "r17_fast_g.rs"
EXPECTED_FAST_G = "2b9ded2a3c8330239bdb0ad581785750eab71c54b069ad7764661d7058c02698"
TABLES = "r17_cyclic_tables.rs"
APPLY = "cyclic_g_apply.rs"
PACK_TABLES_SHA = "68cfaf37ab5330e4efbf61fd0dd5ab8adffb7d35f41c05f81f2d7f7cf89bb1bd"
PACK_APPLY_SHA = "8f9d5d0198bec367bedf571fa696cc77bfb682386cf61a887c3113435386fc31"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def replace_once(s, old, new, label):
    n = s.count(old)
    if n != 1:
        raise SystemExit(f"{label}: expected one match, found {n}")
    return s.replace(old, new, 1)

def cyclic_checks():
    return Path(__file__).with_name("r17_cyclic_g_check.rs").read_text()

def transform(source):
    source = replace_once(source, "        (2048,false) => fft_fixed::<2048,false>(a),\n        (2048,true) => fft_fixed::<2048,true>(a),", "        (1024,false) => fft_fixed::<1024,false>(a),\n        (1024,true) => fft_fixed::<1024,true>(a),\n        (2048,false) => fft_fixed::<2048,false>(a),\n        (2048,true) => fft_fixed::<2048,true>(a),", "1024 FFT dispatch")
    source = replace_once(source, "assert!(matches!(n,64|128|256|2048));", "assert!(matches!(n,64|128|256|1024|2048));", "reference FFT sizes")
    source = replace_once(source, "for n in [64usize,128,256,2048] {", "for n in [64usize,128,256,1024,2048] {", "fixed FFT controls")
    source = replace_once(source, "pub(super) fn apply(coins: &[K; 271], out: &mut [K; 1024]) {", "pub(super) fn apply_2048_reference(coins: &[K; 271], out: &mut [K; 1024]) {", "retain old G reference")
    source += "\ninclude!(\"cyclic_g_apply.rs\");\n\npub(super) fn apply(coins: &[K; 271], out: &mut [K; 1024]) {\n    apply_cyclic_1024(coins, out);\n}\n" + cyclic_checks()
    source = replace_once(source, "pub(super) fn check() {", "pub(super) fn check() {\n    check_cyclic();", "cyclic controls")
    return source

def instrument_apply(source):
    """Keep the old three Solana CU markers in the staged implementation.

    The downloaded pack remains hash-pinned; only the staged copy is
    instrumented so profiler breakdowns remain comparable to R38.
    """
    source = replace_once(source, "    // Compute BEFORE numerator/output overwrite.",
        '    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-tree-start"); solana_program::log::sol_log_compute_units(); }\n    // Compute BEFORE numerator/output overwrite.', "tree-start marker")
    source = replace_once(source, "    cyclic_numerator_into(coins, out, &mut work);",
        '    cyclic_numerator_into(coins, out, &mut work);\n    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-tree-end"); solana_program::log::sol_log_compute_units(); }', "tree-end marker")
    source = replace_once(source, "    for component in 0..2 {", "    for component in 0..2 {", "component loop")
    source = replace_once(source, "    }\n}\n", '    }\n    #[cfg(target_os="solana")] { solana_program::msg!("R17:G-fft-end"); solana_program::log::sol_log_compute_units(); }\n}\n', "fft-end marker")
    return source

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.output.exists(): raise SystemExit(f"output exists: {args.output}")
    src = args.stage / FAST_G
    control_path = args.stage / 'r17-compact-control.json'
    if not src.is_file() or not control_path.is_file(): raise SystemExit('R38 stage missing source/control')
    control = json.loads(control_path.read_text())
    root = args.stage / EXPERIMENTS
    for name, expected in control.get('files', {}).items():
        path = root / name
        if not path.is_file() or sha(path) != expected: raise SystemExit(f'control pin mismatch: {name}')
    for name, expected in control.get('core_files', {}).items():
        path = args.stage / name
        if not path.is_file() or sha(path) != expected: raise SystemExit(f'core pin mismatch: {name}')
    if sha(src) != EXPECTED_FAST_G: raise SystemExit('R38 r17_fast_g is not the retained R24-derived source')
    pack_tables = Path(__file__).with_name(TABLES)
    pack_apply = Path(__file__).with_name('r17_cyclic_g_apply.rs')
    if sha(pack_tables) != PACK_TABLES_SHA or sha(pack_apply) != PACK_APPLY_SHA: raise SystemExit('local cyclic pack hash mismatch')
    old = src.read_bytes(); new = transform(old.decode()).encode()
    shutil.copytree(args.stage, args.output)
    out_root = args.output / EXPERIMENTS
    (out_root / TABLES).write_bytes(pack_tables.read_bytes())
    staged_apply = instrument_apply(pack_apply.read_text())
    (out_root / APPLY).write_text(staged_apply)
    (out_root / FAST_G.name).write_bytes(new)
    after = sha(out_root / FAST_G.name)
    meta = json.loads((args.output / 'r17-sbf-probe.json').read_text())
    meta['cyclic_g'] = {FAST_G.name: {'before_sha256': sha(src), 'after_sha256': after}}
    meta['cyclic_g_files'] = {TABLES: sha(out_root / TABLES), APPLY: sha(out_root / APPLY)}
    meta['cyclic_g_source_pack'] = {'manifest': 'aspis-r17-cu-review-20260921/MANIFEST.json', 'tables_sha256': PACK_TABLES_SHA, 'apply_sha256': PACK_APPLY_SHA, 'reference_fft_sha256': EXPECTED_FAST_G}
    meta['sbf_built'] = False
    (args.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
    control['bin'] = 'r17-tensor-check'
    control.setdefault('files', {})[FAST_G.name] = after
    control['files'][TABLES] = sha(out_root / TABLES)
    control['files'][APPLY] = sha(out_root / APPLY)
    control['cyclic_g'] = {'before_sha256': sha(src), 'after_sha256': after, 'cyclic_g_files': meta['cyclic_g_files'], 'reference_fft_sha256': EXPECTED_FAST_G, 'sbf_built': False}
    (args.output / 'r17-compact-control.json').write_text(json.dumps(control, indent=2) + '\n')
    (args.output / 'r17_cyclic_g.patch').write_text(''.join(__import__('difflib').unified_diff(old.decode().splitlines(True), new.decode().splitlines(True), fromfile=str(FAST_G), tofile=str(FAST_G))))

if __name__ == '__main__': main()
