"""D583 focused structural certificate; no Lean/runtime-instance claim."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

E = Path('evidence/pv-evh10-20261102')
REV = '4ea2abfcc3a50f1b6e766ed41ff07cf815085a87'
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest = json.loads((E / 'binary-correspondence-D581.json').read_text())
raw = (E / 'out-N91601.log').read_bytes()
assert sha(raw) == manifest['analysis_sha256']
x = json.loads(raw)
assert x['binary']['sha256'] == 'da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'

def function(name):
    return next(f['disassembly'] for f in x['functions'] if name in f['header'])

def instruction(asm, pc, operand):
    line = next(l for l in asm.splitlines() if re.match(r'\s*' + pc + ':', l))
    assert operand in line, (pc, line)

plan = function('plan::prove')
retry = function('prover::retry_attempt')
entropy = function('generate_for_mask_nonce')
for asm, pc, op in [
    (plan, '527b1', 'push   $0x0'), (plan, '527b3', 'push   %r15'),
    (plan, '527b5', 'call   5c990'),
    (retry, '5c99a', 'sub    $0x108,%rsp'),
    (retry, '5c9a4', 'mov    0x148(%rsp),%rbp'),
    (retry, '5c9ac', 'cmp    $0x7,%rbp'),
    (retry, '5c9b0', 'jbe    5c9b8'),
    (retry, '5c9ff', 'inc    %rbp'),
    (retry, '5ca02', 'mov    %rbp,0x100(%rdx)'),
    (retry, '5ca09', 'lea    0x40(%rsp),%rdi'),
    (retry, '5ca0e', 'lea    0x10(%rsp),%rsi'),
    (retry, '5ca13', '# 1e80a0'),
    (retry, '5cab6', 'sub    $0x8,%rsp'),
    (retry, '5cadb', 'push   %r14'),
    (retry, '5cae3', 'add    $0x10,%rsp'),
    (retry, '5caff', 'jne    5cb86'),
    (retry, '5cb18', 'push   %rbp'),
    (retry, '5cb19', 'push   0x148(%rsp)'),
    (retry, '5cb20', 'call   5c990'),
    (entropy, '1457aa', 'sub    $0xe8,%rsp'),
    (entropy, '1457e0', 'xor    %ebp,%ebp'),
    (entropy, '1458e1', 'inc    %rbp'),
    (entropy, '1458e4', 'cmp    $0x10,%rbp'),
    (entropy, '1458f1', 'jne    1457ef'),
]:
    instruction(asm, pc, op)
assert len(re.findall(r'call\s+5c990\b', retry)) == 1
for asm in [plan, retry, entropy]:
    prefix = asm.split('sub    $')[0]
    assert len(re.findall(r'\bpush\s+%', prefix)) == 6
assert plan.count('sub    $0x1000,%rsp') == 5
instruction(plan, '4f3a5', 'sub    $0x2a8,%rsp')

sources = []
for entry in manifest['sources']:
    body = subprocess.check_output(['git', 'show', REV + ':' + entry['path']])
    assert sha(body) == entry['sha256']
    sources.append(dict(path=entry['path'], revision=REV, sha256=sha(body)))

def source(suffix):
    path = next(s['path'] for s in sources if s['path'].endswith(suffix))
    return subprocess.check_output(['git', 'show', REV + ':' + path], text=True)

prover = source('/prover.rs')
assert 'pub const ATTEMPT_CAP: usize = 8;' in prover
body = prover[prover.index('fn retry_attempt('):prover.index('/// Test-only injection')]
assert 'if k>=ATTEMPT_CAP { return Err(Error::AttemptsExhausted); }' in body
assert 'let attempt=next_attempt(k)?;' in body
assert body.count('=>retry_attempt(') == 1
assert 'Err(Error::Rejected)=>retry_attempt(public,compiled,variant,hash,nonce_store,next_attempt,k+1)' in body
assert 'retry_attempt(public,compiled,variant,hash,nonce_store,next_attempt,0)' in prover
ent = source('/state_only_entropy.rs')
assert re.search(r'const ENTROPY_RETRY_LIMIT\s*:\s*usize\s*=\s*16\s*;', ent)
start = ent.index('    pub fn generate_for_mask_nonce(')
body = ent[start:ent.index('    pub fn mask_nonce(', start)]
assert 'while retry<limit {' in body and 'retry+=1;' in body
assert body.count('generate_for_mask_nonce(') == 1
assert 'generate_for_mask_nonce(proof_account(k))' in source('/RealR1_client.rs')
assert 'accounts.nonce(k)' in source('/plan.rs')

# Small control-state certificate for the source/binary induction in the note.
# All reject/stop outcomes are considered; this is not a native experiment.
states = [(0, 1)]
for k, depth in states:
    assert k == depth - 1 and k <= 8
    if k < 8:
        states.append((k + 1, depth + 1))
assert len(states) == 9
assert max(depth for k, depth in states if k < 8) == 8
entropy_delta = 8 + 6 * 8 + 232
retry_delta = 16 + 8 + 6 * 8 + 264
plan_delta = 6 * 8 + 0x52a8
assert (entropy_delta, retry_delta, plan_delta) == (288, 336, 21208)
assert entropy_delta != -manifest['frames']['entropy_sp_relative_to_retry_sp']
assert entropy_delta + 16 == 304 and entropy_delta + 64 == 352
assert 352 + 97 == 449
assert (8 - 6 * 8 - 232) % 16 == 0
assert 8 * retry_delta + entropy_delta == 2976
assert plan_delta + 2976 == 24184
assert plan_delta + 9 * retry_delta == 24232
# Earlier D572 caller binding already has the correct saved-register arithmetic.
caller = Path('tools/pv-evh10-20261102/caller_binding.py').read_text()
assert 'caller_offset=288,mask_offset=304,result_offset=352' in caller

inputs = [E / 'out-N91601.log', E / 'binary-correspondence-D581.json',
          E / 'PHYSICAL-D581.md', E / 'STACK-RESOURCE-D583.md',
          E / 'FRAME-ENTRY-D583.md', Path(__file__),
          Path('tools/pv-evh10-20261102/caller_binding.py')]
result = dict(
    evidence_class='source/binary-structural plus OS-model; V370 compiler-cohort',
    adopted_binary_sha256=x['binary']['sha256'], sources=sources,
    inputs=[dict(path=str(p), sha256=sha(p.read_bytes())) for p in inputs],
    control_states=[dict(k=k, live_retry_frames=d) for k, d in states],
    entropy_reached_live_retry_max=8, cap_check_live_retry_max=9,
    entropy_iterations_per_activation_max=16, initializer_visits_max=128,
    frames=dict(entropy_delta=entropy_delta, retry_delta=retry_delta,
                plan_delta=plan_delta, initializer_spine_max=2976,
                initializer_from_plan_entry_max=24184, cap_from_plan_entry_max=24232,
                mask_offset=304, result_offset=352),
    world_answers=['granted', 'exhausted'], failure_branch_retained=True,
    sole_frame_interpretation_dependency='OWNER_actual_prefix (shared pv-evhB4 after lead merge)',
    conditional_frame_interface='FRAME-ENTRY-D583.md',
    actual_domain_implemented=False, lean_frame_proof=False,
    runtime_stack_instance_installed=False, full_client_stack_bound=False,
    full_V400_discharged=False, rows_removed=[], trust_fields_added=[])
out = E / 'stack-resource-D583.json'
if '--check' in sys.argv:
    assert json.loads(out.read_text()) == result
else:
    out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS D583 source/binary depth certificate; corrected caller offsets; both resource branches specified; no actual runtime claim')
