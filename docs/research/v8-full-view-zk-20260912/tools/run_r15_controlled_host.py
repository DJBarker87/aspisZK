#!/usr/bin/env python3
"""Four complete host executions; final two use ONE fixed six-cell function.

The first pair only locates query inputs. The second pair is replayed from
scratch against SHA-256 plus the SAME fixed table, with no adaptive changes.
This is an execution/certificate experiment, not a random-oracle law.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def sha(data):
    return hashlib.sha256(data).hexdigest()


def raw_pair_statistic(proof, queries):
    """Column zero at q4/q6 in the literal SLOT-major C1 records."""
    assert len(queries) == 22 and len(set(queries)) == 22
    assert len(proof) >= 697 * 16 + 76 + 22 * 621
    coefficients = [1508290849, 1480589898, 639192798, 666893749, 2147483646, 0, 1, 0]
    modulus = 2 ** 31 - 1
    values = []
    for query in [4, 6]:
        offset = 697 * 16 + 76 + queries.index(query) * 621
        packed = int.from_bytes(proof[offset:offset + 403], 'little')
        values.extend((packed >> (31 * slot * 26)) & modulus for slot in range(4))
    assert all(value < modulus for value in values)
    return sum(a * b for a, b in zip(coefficients, values)) % modulus


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--analyze-existing', action='store_true',
                        help='analyze retained logs/bodies without repeating any host run')
    args = parser.parse_args()
    binary, stage, output = args.binary.resolve(), args.stage.resolve(), args.output.resolve()
    if output.exists() and not args.analyze_existing:
        parser.error('output must not exist')
    if not args.analyze_existing:
        output.mkdir(parents=True)
    metadata = json.loads((stage / 'r15-controlled-stage.json').read_text())
    assert metadata['diagnostic_only'] is True
    for item in metadata['instrumentation']:
        assert sha((stage / item['path']).read_bytes()) == item['after_sha256']
    edited = {item['path'] for item in metadata['instrumentation']}
    for item in metadata['generated_v4_inputs']:
        if item['path'] not in edited:
            assert sha((stage / item['path']).read_bytes()) == item['sha256']
    assert sha((stage / 'docs/research/v8-no-work-100-20260907/experiments/r15_controlled_oracle.rs').read_bytes()) == metadata['oracle_module_sha256']
    if 'query_audit_module_sha256' in metadata:
        assert sha((stage / 'docs/research/v8-no-work-100-20260907/experiments/r15_query_audit.rs').read_bytes()) == metadata['query_audit_module_sha256']
    runs = []

    def run(name, world, table=None):
        env = os.environ.copy()
        for key in ['ASPIS_V8_MAX_FRONTIER_SCAN', 'ASPIS_V8_LIVE_CONTEXT',
                    'ASPIS_V8_COMPLETE_CONTEXT', 'ASPIS_R15_ORACLE_TABLE']:
            env.pop(key, None)
        env.update(NO_DNA='1', ASPIS_V8_POSITIVE_CASE='honest', ASPIS_R15_SELECTED_SECOND=str(world))
        if table is not None:
            env['ASPIS_R15_ORACLE_TABLE'] = str(table)
        if args.analyze_existing:
            log = (output / (name + '.log')).read_text()
            # Recorded acceptance is not alone proof of exit 0; reject a
            # /usr/bin/time nonzero/signal diagnostic and retain that boundary.
            assert 'Command exited with non-zero status' not in log
            assert 'terminated' not in log.lower()
            status_path = output / (name + '.exit.json')
            exit_status = json.loads(status_path.read_text())['exit'] if status_path.exists() else None
            assert exit_status in [None, 0]
        else:
            completed = subprocess.run(['/usr/bin/time', '-l', str(binary), str(output / name)],
                cwd=stage, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            log = completed.stdout
            (output / (name + '.log')).write_text(log)
            exit_status = completed.returncode
            (output / (name + '.exit.json')).write_text(json.dumps({'exit': exit_status}) + '\n')
            assert completed.returncode == 0, (name, completed.returncode, log[-4000:])
        assert '"accepted":true' in log
        entry = re.search(r'R15_Q22_ENTRY ([0-9a-f]{64})', log).group(1)
        queries = ast.literal_eval(re.search(r'R15_Q22_RESULT (\[[^\n]+\])', log).group(1))
        proof = (output / name / 'proof-1.bin').read_bytes()
        record = {'name': name, 'world': world,
                  'exit': exit_status,
                  'exit_evidence': 'not re-executed; consult original command output if exit metadata is absent' if args.analyze_existing else 'subprocess returncode',
                  'wall_seconds': float(re.search(r'([0-9.]+) real\s', log).group(1)),
                  'entry_state': entry, 'queries': queries,
                  'proof_sha256': sha(proof), 'proof_bytes': len(proof),
                  'peak_rss_bytes': int(re.search(r'(\d+)\s+maximum resident set size', log).group(1)),
                  'swaps': int(re.search(r'(\d+)\s+swaps', log).group(1))}
        runs.append(record)
        print(json.dumps(record), flush=True)
        return record

    base = [run('locate-' + str(world), world) for world in range(2)]
    queries = [4, 6] + [1000 + 7919 * i for i in range(20)]
    assert len(set(queries)) == 22 and max(queries) < 2 ** 18
    words = queries + [0, 1]  # unused tail of the third block is retained
    cells = {}
    for record in base:
        state = bytes.fromhex(record['entry_state'])
        for block in range(3):
            key = state + b'\x01'
            answer = b''.join(v.to_bytes(4, 'little') for v in words[8 * block:8 * block + 8])
            assert key not in cells or cells[key] == answer
            cells[key] = answer
            # Output and advance use the same old state; only output changes.
            state = hashlib.sha256(state + b'\x02').digest()
    table = output / 'fixed-oracle.bin'
    table_bytes = b'R15ORCL1' + b''.join(key + value for key, value in sorted(cells.items()))
    if args.analyze_existing:
        assert table.read_bytes() == table_bytes
    else:
        table.write_bytes(table_bytes)
    final = [run('fixed-' + str(world), world, table) for world in range(2)]
    for world in range(2):
        assert final[world]['entry_state'] == base[world]['entry_state'], 'override affected earlier history'
        assert final[world]['queries'] == queries
        before = (output / ('locate-' + str(world)) / 'proof-1.bin').read_bytes()
        after = (output / ('fixed-' + str(world)) / 'proof-1.bin').read_bytes()
        # All serialized values produced before the q22 call: the initial
        # claim, ten semantic rounds, 87 point fields, OOD and inactive fields,
        # first relation polynomial, Final256, both roots and zero nonces.
        assert before[:423 * 16] == after[:423 * 16]
        assert before[441 * 16:697 * 16 + 76] == after[441 * 16:697 * 16 + 76]
    public = {}
    for name in ['public.bin', 'transition.bin', 'binding.bin']:
        left = (output / 'fixed-0' / name).read_bytes()
        right = (output / 'fixed-1' / name).read_bytes()
        assert left == right, ('not same public input', name)
        public[name] = sha(left)
    modulus = 2 ** 31 - 1
    stats = []
    for world in range(2):
        proof = (output / ('fixed-' + str(world)) / 'proof-1.bin').read_bytes()
        stats.append(raw_pair_statistic(proof, final[world]['queries']))
    assert (stats[1] - stats[0]) % modulus == 490597912
    report = {'scope': 'same-public complete source-derived diagnostic executions under one fixed function; NOT a probability theorem',
              'source_revision': metadata['source_revision'], 'binary_sha256': sha(binary.read_bytes()),
              'stage_instrumentation': metadata['instrumentation'], 'oracle_cells': len(cells),
              'oracle_table_sha256': sha(table.read_bytes()), 'public_sha256': public,
              'fixed_oracle_cells': [{'input_hex': key.hex(), 'answer_hex': value.hex()} for key, value in sorted(cells.items())],
              'raw_statistics': stats, 'statistic_delta': 490597912, 'runs': runs,
              'production_source_changed': False, 'actual_random_oracle_advantage_established': False}
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
