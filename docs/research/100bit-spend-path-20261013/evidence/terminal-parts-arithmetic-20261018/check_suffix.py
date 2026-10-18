"""Check the arithmetic suffix against the retained generated source excerpt."""
from pathlib import Path
import argparse
import hashlib
import json
import re

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--generated', type=Path,
                    default=here / 'generated-terminal-parts.lean.txt')
parser.add_argument('--target', type=Path,
                    default=here.parent.parent / 'lean/TerminalPartsArithmeticExact.lean')
args = parser.parse_args()
generated = args.generated.read_text()
start = generated.index('def pool_v1.pair_forest_semantic_terminal.terminal_parts\n')
generated = generated[start:]
suffix = generated[generated.index('    let q ←'):
                   generated.index('    ok (core.result.Result.Ok')]
suffix = suffix.replace('let original ← field.QM31.add q3 q7',
                        'field.QM31.add q3 q7')
target = args.target.read_text()
body = target[target.index('  let q ←'):target.index('\ntheorem run_exact')]
normalize = lambda text: re.sub(r'\s+', '', text)
if normalize(suffix) != normalize(body):
    raise SystemExit('FAIL: terminal arithmetic suffix changed')
print(json.dumps({
    'status': 'pass',
    'target_sha256': hashlib.sha256(args.target.read_bytes()).hexdigest(),
    'generated_input_sha256': hashlib.sha256(args.generated.read_bytes()).hexdigest(),
    'normalization': 'Whitespace and final local return binding only.',
    'scope': 'Arithmetic suffix only; not a production-source refinement proof.'
}, indent=2))
