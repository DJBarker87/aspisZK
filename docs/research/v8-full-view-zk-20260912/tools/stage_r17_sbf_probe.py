#!/usr/bin/env python3
"""Create a fresh R17 candidate SBF probe; never substitute an old verifier.

This preserves the host candidate's deferred/dense double-check. It measures
that implementation, not an optimized final repair or a complete transaction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from reconstruct_generated_inputs import EXPERIMENTS

ENTRY = r'''

// R17 read-only local SVM probe. No settlement/deployment adapter.
#[cfg(v8_performance_sbf)]
solana_program::entrypoint!(r17_probe_entry);
#[cfg(target_os="solana")]
#[global_allocator]
static R17_ALLOC: solana_program::entrypoint::BumpAllocator =
    solana_program::entrypoint::BumpAllocator {
        start: solana_program::entrypoint::HEAP_START_ADDRESS as usize,
        len: 256 * 1024,
    };
#[cfg(v8_performance_sbf)]
fn r17_probe_entry(
    _id: &solana_program::pubkey::Pubkey,
    accounts: &[solana_program::account_info::AccountInfo],
    instruction: &[u8],
) -> solana_program::entrypoint::ProgramResult {
    use solana_program::program_error::ProgramError;
    if accounts.len() != 3 || instruction.len() != 32 ||
        accounts.iter().any(|a| a.is_writable) {
        return Err(ProgramError::InvalidArgument);
    }
    let body = accounts[0].try_borrow_data()?;
    let public = accounts[1].try_borrow_data()?;
    let transition = accounts[2].try_borrow_data()?;
    performance_verifier::verify(&body, instruction.try_into().unwrap(),
        &public, &transition).map_err(ProgramError::Custom)
}
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    subprocess.run([sys.executable, str(Path(__file__).with_name('stage_r17_two_channel_host.py')),
                    '--repo', str(a.repo.resolve()), '--output', str(a.output.resolve())], check=True)
    out = a.output.resolve()
    exporter = out / EXPERIMENTS / 'r17_export_basis.rs'
    exporter.write_text('''// Export the actual host constructor, not a second inventory algorithm.
#[path="r16_basis_transport.rs"] mod basis;
fn main() {
    let map = basis::Transport::new();
    assert_eq!(map.order.len(), 1024);
    assert_eq!(map.inactive.len(), 1024);
    let mut sorted = map.order.clone(); sorted.sort_unstable();
    assert_eq!(sorted, (0..1024).collect::<Vec<_>>());
    println!("pub const ORDER: [usize; 1024] = {:?};", map.order);
    println!("pub const INACTIVE: [bool; 1024] = {:?};", map.inactive);
}
''')
    host_manifest = out / EXPERIMENTS / 'performance-host/Cargo.toml'
    host_manifest.write_text(host_manifest.read_text() + '''
[[bin]]
name = "r17-export-basis"
path = "../r17_export_basis.rs"
''')
    source = out / EXPERIMENTS / 'relation_callback.rs'
    before = source.read_bytes()
    source.write_bytes(before + ENTRY.encode())
    manifest = out / EXPERIMENTS / 'performance-sbf/Cargo.toml'
    text = manifest.read_text()
    assert text.count('path = "lib.rs"') == 1
    manifest.write_text(text.replace('path = "lib.rs"', 'path = "../relation_callback.rs"'))
    stage = json.loads((out / 'r17-stage.json').read_text())
    flags = stage['rustflags'].split()
    pairs = [flags[i:i+2] for i in range(0, len(flags), 2)]
    pairs = [v for v in pairs if v not in [['--cfg', 'v8_performance'],
                                          ['--cfg', 'v8_payment_extraction']]]
    rustflags = ' '.join(x for pair in pairs for x in pair) + ' --cfg v8_performance_sbf'
    (out / 'r17-sbf-probe.json').write_text(json.dumps({
        'profile': stage['profile'], 'rustflags': rustflags,
        'features': 'selected-v7-kernels', 'manifest': str(manifest.relative_to(out)),
        'callback_before_sha256': hashlib.sha256(before).hexdigest(),
        'callback_after_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope': 'candidate verifier only; no settlement; double verification retained',
        'privacy_proved': False, 'soundness_preservation_proved': False,
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
