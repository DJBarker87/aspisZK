from pathlib import Path
import re

root = Path(__file__).resolve().parent
pairs = [
    (root / 'extraction/generated-Types.raw.lean',
     root / 'proof/AspisR1Post25Sampler.Types.sanitized.lean'),
    (root / 'extraction/generated-Funs.raw.lean',
     root / 'proof/AspisR1Post25Sampler.Funs.sanitized.lean'),
]

def sanitize(text: str) -> str:
    for option, cli in [('maxHeartbeats', 'max-heartbeats'), ('maxRecDepth', 'max-recdepth')]:
        text = re.sub(
            rf'\n/\- You can set the `{option}` value with the `-{cli}` CLI option \-/\n'
            rf'set_option {option} [^\n]*\n',
            '\n', text)
    return text

for raw_path, compiled_path in pairs:
    expected = sanitize(raw_path.read_text())
    actual = compiled_path.read_text()
    if expected != actual:
        raise SystemExit(f'sanitized copy differs beyond resource-option comment/setting lines: {compiled_path.name}')
    if re.search(r'^set_option (?:maxHeartbeats|maxRecDepth)', actual, re.M):
        raise SystemExit(f'resource-option override remains: {compiled_path.name}')
    print(f'PASS {raw_path.name} -> {compiled_path.name}')
