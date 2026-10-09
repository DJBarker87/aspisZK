#!/usr/bin/env python3
"""Research-only chosen-nonce host. SHA-256 and verification are unchanged.

This is not the ordinary fixed-zero-nonce prover distribution. It tests
whether an accepted disclosure can be constructed without hash overrides.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from reconstruct_generated_inputs import EXPERIMENTS, one_replace


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    subprocess.run([sys.executable, str(Path(__file__).with_name('stage_r15_host.py')),
                    '--repo', str(args.repo.resolve()), '--output', str(out)], check=True)
    edits = []

    def edit(relative, substitutions):
        path = out / relative
        before = path.read_bytes()
        text = before.decode()
        for old, new, label in substitutions:
            text = one_replace(text, old, new, label)
        after = text.encode()
        path.write_bytes(after)
        edits.append({'path': str(relative), 'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(after).hexdigest()})

    edit(EXPERIMENTS / 'recovered_witness.rs', [
        ('two_outputs(leaf,dig(900))', 'two_outputs(leaf,leaf)', 'same-public fixture'),
        ('pair_leaf:pair,selected_second:false,',
         'pair_leaf:pair,selected_second:std::env::var("ASPIS_R15_SELECTED_SECOND").as_deref()==Ok("1"),',
         'witness selector')])
    edit(EXPERIMENTS / 'performance.rs', [
        ('let mut nonce=[0u8;24];',
         'let mut nonce=[0u8;24];\n    let chosen:u64=std::env::var("ASPIS_R15_FINAL_NONCE").unwrap_or_else(|_|"0".into()).parse().unwrap();\n    nonce[16..24].copy_from_slice(&chosen.to_le_bytes());',
         'research-only chosen final nonce')])
    edit(EXPERIMENTS / 'relation_callback.rs', [
        ('p.t.absorb(label::GRIND_NONCE,&nonces[16..24]);',
         'eprintln!("R15_PRE_NONCE {}",p.t.diagnostic_state().iter().map(|b|format!("{b:02x}")).collect::<String>());p.t.absorb(label::GRIND_NONCE,&nonces[16..24]);',
         'read-only pre-nonce state'),
        ('p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");',
         'eprintln!("R15_Q22_RESULT {q:?}");p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");',
         'read-only query result')])
    metadata = json.loads((out / 'r15-stage.json').read_text())
    metadata.update(diagnostic_only=True, instrumentation=edits,
                    hash_overrides=False, ordinary_nonce_policy=False,
                    scope='same-public fixture, chosen final nonce, ordinary SHA-256; no probability claim')
    (out / 'r15-sha-nonce-stage.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
