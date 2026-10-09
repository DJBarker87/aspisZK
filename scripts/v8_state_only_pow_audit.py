#!/usr/bin/env python3
"""Audit the omitted PoW instruction blocks in the measured, pinned SBF ELF.

Usage: script llvm-objdump unstripped.so measured.so evidence.json
This does not build, modify, or execute either ELF. It deliberately fails if
the compiler no longer emits the reviewed instruction pattern.
"""
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

objdump, unstripped_path, measured_path, output_path = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()

def text_section(data):
    assert data[:6] == b'\x7fELF\x02\x01'
    offset = struct.unpack_from('<Q', data, 40)[0]
    size, count, string_index = struct.unpack_from('<HHH', data, 58)
    sections = [struct.unpack_from('<IIQQQQIIQQ', data, offset + i * size) for i in range(count)]
    strings = sections[string_index]
    names = data[strings[4]:strings[4] + strings[5]]
    for section in sections:
        name = names[section[0]:].split(b'\0', 1)[0]
        if name == b'.text':
            return data[section[4]:section[4] + section[5]]
    raise AssertionError('missing .text')

unstripped = Path(unstripped_path).read_bytes()
measured = Path(measured_path).read_bytes()
assert text_section(unstripped) == text_section(measured)
disassembly = subprocess.check_output([objdump, '--demangle', '-d', unstripped_path], text=True)
functions = {}
current = None
for line in disassembly.splitlines():
    match = re.match(r'^[0-9a-f]+ <(.+)>:$', line)
    if match:
        current = match[1].rsplit('::h', 1)[0]
        functions[current] = []
    elif current and re.match(r'^\s+[0-9a-f]+:', line):
        address = int(line.split(':', 1)[0], 16)
        operation = line.split('\t')[-1].strip()
        functions[current].append((address, operation))

prefix = 'aspis_core::state_only_prefix::'
replay = functions[prefix + 'run_full_with_context']
batch = functions[prefix + 'begin_schedule_with_context']
grind = functions['aspis_core::transcript::Transcript::grinding_ok']
strict = functions[prefix + 'run_atomic_state_only_transcript_schedule_host_v3']
diagnostic = functions[prefix + 'run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3']
assert len(strict) == len(diagnostic) == 6
assert [op.split()[0] for _, op in strict] == [op.split()[0] for _, op in diagnostic]

pattern = ['callx', 'jeq', 'ldxdw', 'jeq', 'ldxdw', 'be64', 'neg64', 'and64', 'rsh64', 'jne']
starts = [i for i in range(len(replay) - len(pattern))
          if [op.split()[0] for _, op in replay[i:i + len(pattern)]] == pattern]
assert len(starts) == 1, starts
start = starts[0]
block = replay[start:start + len(pattern)]
skipped = block[4:]
assert len(skipped) == 6

def call_target(instruction):
    address, op = instruction
    return address + 8 + int(op.split()[1], 16) * 8

batch_calls = [i for i in batch if i[1].startswith('call ') and call_target(i) == grind[0][0]]
final_calls = [i for i in replay if i[1].startswith('call ') and call_target(i) == grind[0][0]]
assert len(batch_calls) == len(final_calls) == 1
assert sum(op.startswith('callx ') for _, op in grind) == 1

def rendered(instructions):
    return [f'0x{address:x}: {op}' for address, op in instructions]

record = {
    'label': 'unmined diagnostic path (PoW rejection disabled)',
    'measured_elf_sha256': sha(measured), 'unstripped_elf_sha256': sha(unstripped),
    'identical_text_sections': True, 'text_section_sha256': sha(text_section(measured)),
    'source_sites': {
        'batch': 'crates/aspis-core/src/state_only_prefix.rs::begin_schedule_with_context (batch_ok)',
        'folds': 'crates/aspis-core/src/state_only_prefix.rs::run_full_with_context (fold_ok)',
        'final': 'crates/aspis-core/src/state_only_prefix.rs::run_full_with_context (final_ok)',
        'predicate': 'crates/aspis-core/src/transcript.rs:52',
        'hash_input': 'crates/aspis-core/src/transcript.rs:593',
    },
    'logical_full_replay_hashes': 6, 'hash_input_bytes_each': 41,
    'hash_input_slices': [32, 1, 8], 'logical_64bit_threshold_comparisons': 6,
    'hashes_present_in_diagnostic_binary': 6,
    'additional_hashes_for_strict_replay': 0,
    'additional_64bit_comparisons_for_strict_replay': 4,
    'skipped_instructions_per_fold': 6, 'fold_count': 4,
    'omission_upper_bound_cu': 24,
    'bound_scope': 'PoW-only successful-path instruction difference in this compiled replay; not a mined-proof total prediction',
    'explanation': 'Batch/final already hash and compare; their successful paths are no longer than the diagnostic paths. Each of four folds retains its hash but skips the six listed instructions when check_pow is false. These are ordinary one-CU SBF instructions, with no syscall. Schedule wrappers have equal instruction counts. Nonce absorption is unchanged.',
    'fold_block_including_unconditional_hash': rendered(block),
    'omitted_fold_block': rendered(skipped),
    'batch_call': rendered(batch_calls), 'final_call': rendered(final_calls),
    'grinding_ok_function': rendered(grind),
    'strict_schedule_wrapper': rendered(strict),
    'diagnostic_schedule_wrapper': rendered(diagnostic),
}
Path(output_path).write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: record[k] for k in ('measured_elf_sha256', 'omission_upper_bound_cu')}))
