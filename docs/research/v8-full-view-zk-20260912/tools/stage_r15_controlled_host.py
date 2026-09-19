#!/usr/bin/env python3
"""Create a NEW named witness/oracle diagnostic from the authenticated host.

Never describe this instrumented program or its chosen deterministic oracle
as the pinned production program or a random-oracle distribution theorem.
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
    def edit(relative, transform):
        path = out / relative
        before = path.read_bytes()
        after = transform(before.decode()).encode()
        path.write_bytes(after)
        edits.append({'path': str(relative), 'before_sha256': hashlib.sha256(before).hexdigest(),
                      'after_sha256': hashlib.sha256(after).hexdigest()})
    def witness(text):
        text = one_replace(text, 'two_outputs(leaf,dig(900))', 'two_outputs(leaf,leaf)',
                           'same-public duplicate commitment')
        return one_replace(text, 'pair_leaf:pair,selected_second:false,',
            'pair_leaf:pair,selected_second:std::env::var("ASPIS_R15_SELECTED_SECOND").as_deref()==Ok("1"),',
            'research witness selector')
    edit(EXPERIMENTS / 'recovered_witness.rs', witness)
    def oracle(text):
        text = one_replace(text, 'use corelib::{', 'mod r15_controlled_oracle;\nuse corelib::{',
                           'research oracle module')
        text = one_replace(text, 'let digest=h.finalize().into();',
            'let digest=r15_controlled_oracle::answer(parts,h.finalize().into());',
            'fixed function override')
        text = one_replace(text, 'let q=p.t.challenge_queries_without_replacement(22,1<<18,64)',
            'r15_controlled_oracle::query_entry(p.t.diagnostic_state());\n    let q=p.t.challenge_queries_without_replacement(22,1<<18,64)',
            'read-only query entry observation')
        return one_replace(text, 'p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");',
            'r15_controlled_oracle::query_result(&q);\n    p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");',
            'read-only query result observation')
    edit(EXPERIMENTS / 'relation_callback.rs', oracle)
    module = Path(__file__).with_name('r15_controlled_oracle.rs').read_bytes()
    (out / EXPERIMENTS / 'r15_controlled_oracle.rs').write_bytes(module)
    metadata = json.loads((out / 'r15-stage.json').read_text())
    metadata['diagnostic_only'] = True
    metadata['instrumentation'] = edits
    metadata['oracle_module_sha256'] = hashlib.sha256(module).hexdigest()
    metadata['scope'] = 'test-only duplicate witness and fixed deterministic oracle hooks; no distribution claim'
    (out / 'r15-controlled-stage.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps({'diagnostic_stage': str(out), 'edits': edits}, indent=2))


if __name__ == '__main__':
    main()
