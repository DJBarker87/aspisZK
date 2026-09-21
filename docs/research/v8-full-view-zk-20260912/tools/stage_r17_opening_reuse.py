#!/usr/bin/env python3
"""Stage the bounded R36 opening-reuse candidate in a fresh copy."""
import argparse
import difflib
import hashlib
import json
import shutil
from pathlib import Path

TARGET = Path("docs/research/v8-no-work-100-20260907/experiments/r17_host_relation.rs")
QUERY = Path("docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs")
EXPECTED_TARGET_BEFORE = "ddc3ae6ca20a27bf530fe5ef776afaa296847564bd1f919589b35df97e5074da"
EXPECTED_QUERY_SHA256 = "57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1"

def replace_once(s, old, new, label):
    n = s.count(old)
    if n != 1:
        raise SystemExit(f"{label}: expected one match, found {n}")
    return s.replace(old, new, 1)

def make_candidate(s):
    s = replace_once(s,
        "let all = gamma_combine_v6_packed_layer0(&r[..403], &r[403..589], &powers)\n            .map_err(|_| Error::Canonical)?;",
        """let all = query_arithmetic::gamma(&r[..403], &r[403..589], &powers)?;
        #[cfg(not(target_os="solana"))]
        assert_eq!(all, gamma_combine_v6_packed_layer0(&r[..403], &r[403..589], &powers).map_err(|_| Error::Canonical)?);
""",
        "authenticated gamma route")
    s = replace_once(s,
        """        for (x,y) in [(base.x,base.y),(base.x,base.y.neg()),(base.x.neg(),base.y.neg()),(base.x.neg(),base.y)] {
            denoms.push(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)));
        }
""",
        """        let bx = p.abc[1].mul_m31(base.x);
        let cy = p.abc[2].mul_m31(base.y);
        for (j,(x,y)) in [(base.x,base.y),(base.x,base.y.neg()),(base.x.neg(),base.y.neg()),(base.x.neg(),base.y)].into_iter().enumerate() {
            let dx = if j < 2 { bx } else { bx.neg() };
            let dy = if j == 0 || j == 3 { cy } else { cy.neg() };
            denoms.push(p.abc[0].add(dx).add(dy));
            #[cfg(not(target_os="solana"))]
            assert_eq!(denoms.last().copied().unwrap(), p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)));
        }
""",
        "shared denominator products")
    s = replace_once(s,
        """            let iv = if channel == 0 { p.iv } else { iv_g };
            for (slot, (x, y)) in [
""",
        """            let iv = if channel == 0 { p.iv } else { iv_g };
            let iv_delta = iv[1].mul_m31(if p.use_x { base.x } else { base.y });
            for (slot, (x, y)) in [
""",
        "per-channel IV preparation")
    s = replace_once(s,
        """                q[slot] = v
                    .sub(iv[0].add(iv[1].mul_m31(if p.use_x { x } else { y })))
                    .mul(match &inverse_batch {
""",
        """                let same = if p.use_x { slot < 2 } else { slot == 0 || slot == 3 };
                q[slot] = v
                    .sub({
                        #[cfg(not(target_os="solana"))]
                        assert_eq!(if same { iv_delta } else { iv_delta.neg() }, iv[1].mul_m31(if p.use_x { x } else { y }));
                        iv[0].add(if same { iv_delta } else { iv_delta.neg() })
                    })
                    .mul(match &inverse_batch {
""",
        "shared IV sign/product")
    return s

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.output.exists():
        raise SystemExit(f'output already exists: {a.output}')
    before = a.stage / TARGET
    query = a.stage / QUERY
    if not before.is_file() or not query.is_file():
        raise SystemExit('R36 stage is missing target or query_arithmetic source')
    old = before.read_bytes()
    if hashlib.sha256(old).hexdigest() != EXPECTED_TARGET_BEFORE:
        raise SystemExit('R36 target hash does not match the pinned R36 base')
    query_sha = hashlib.sha256(query.read_bytes()).hexdigest()
    if query_sha != EXPECTED_QUERY_SHA256:
        raise SystemExit('query_arithmetic hash does not match the retained optimized source')
    new = make_candidate(old.decode()).encode()
    shutil.copytree(a.stage, a.output)
    (a.output / TARGET).write_bytes(new)
    meta = {
        'candidate': 'r17-opening-reuse-gamma-query-shared-v1',
        'target': str(TARGET),
        'before_sha256': hashlib.sha256(old).hexdigest(),
        'after_sha256': hashlib.sha256(new).hexdigest(),
        'query_arithmetic_sha256': query_sha,
        'control_command': 'cargo run --release --bin aspis-v8-performance-host -- --gamma-controls',
        'changes': ['query_arithmetic::gamma route', 'shared abc denominator products', 'per-channel IV slope product/signs'],
        'preserved': ['canonical gamma before packed G', 'points/domain/error chronology', 'query order and rho', 'both channels and reference check', 'Merkle/authentication path'],
        'no_new_flags': True,
        'diagnostic_only': True,
    }
    diff = difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True), fromfile=f'a/{TARGET}', tofile=f'b/{TARGET}')
    (a.output / 'r17_opening_reuse.patch').write_text(''.join(diff))
    (a.output / 'r17_opening_reuse_pins.json').write_text(json.dumps(meta, indent=2) + '\n')
    stage_meta_path = a.output / 'r17-stage.json'
    if stage_meta_path.is_file():
        stage_meta = json.loads(stage_meta_path.read_text())
        stage_meta.setdefault('opening_reuse', {})[TARGET.name] = {
            'before_sha256': meta['before_sha256'],
            'after_sha256': meta['after_sha256'],
        }
        stage_meta_path.write_text(json.dumps(stage_meta, indent=2) + '\n')
    probe_meta_path = a.output / 'r17-sbf-probe.json'
    if probe_meta_path.is_file():
        probe_meta = json.loads(probe_meta_path.read_text())
        probe_meta.setdefault('opening_reuse', {})[TARGET.name] = {
            'before_sha256': meta['before_sha256'],
            'after_sha256': meta['after_sha256'],
        }
        probe_meta_path.write_text(json.dumps(probe_meta, indent=2) + '\n')
    control_path = a.output / 'r17-compact-control.json'
    if control_path.is_file():
        control = json.loads(control_path.read_text())
        files = control.setdefault('files', {})
        if files.get(TARGET.name) not in (None, meta['before_sha256']):
            raise SystemExit('control target pin does not match the pinned R36 target')
        files[TARGET.name] = meta['after_sha256']
        files[QUERY.name] = query_sha
        control['opening_reuse'] = {
            'target_before_sha256': meta['before_sha256'],
            'target_after_sha256': meta['after_sha256'],
            'query_arithmetic_sha256': query_sha,
            'control_command': meta['control_command'],
            'focused_runner': 'aspis-v8-performance-host',
            'negative_canonical_controls': 'query_arithmetic::controls',
        }
        control_path.write_text(json.dumps(control, indent=2) + '\n')

if __name__ == '__main__':
    main()
