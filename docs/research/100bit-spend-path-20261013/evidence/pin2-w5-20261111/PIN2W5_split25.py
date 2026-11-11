"""Reconstruct the archived row-25 split drafts (JFm_UNCHECKED/JFm_Q25Block00..58,
JFm_Q25SplitAggregate, JFm_Q25SplitReads .lean.txt) from JFm_Q25Hashes.lean.txt.
No committed script produced them; this rule reproduces all 61 archived files
byte for byte from the archived 26 October Hashes text (asserted in 'check').
usage: python3 -I PIN2W5_split25.py check | <Hashes.lean.txt> <outdir>"""
import sys, subprocess
from pathlib import Path
HDR = 'import JFp_SHABlocks\nset_option autoImplicit false\nnamespace AspisR1.JFm_Q25Absorb\nopen JFp_SHA256\n'
def split(s):
    out = {}
    for b in range(59):
        i = s.index(f'namespace B{b:02}\n'); j = s.index(f'end B{b:02}\n') + len(f'end B{b:02}\n')
        out[f'JFm_Q25Block{b:02}.lean.txt'] = HDR + s[i:j] + 'end AspisR1.JFm_Q25Absorb\n'
    e = s.index('end B58\n') + len('end B58\n'); r = s.index('\nnamespace AspisR1.JFm_Q25Read')
    out['JFm_Q25SplitAggregate.lean.txt'] = ''.join(f'import JFm_Q25Block{b:02}\n' for b in range(59)) + 'set_option autoImplicit false\nnamespace AspisR1.JFm_Q25Absorb\nopen JFp_SHA256\n' + s[e:r]
    out['JFm_Q25SplitReads.lean.txt'] = 'import JFp_SHABlocks\nset_option autoImplicit false\n' + s[r:]
    return out
if __name__ == '__main__':
    if sys.argv[1] == 'check':
        g = lambda f: subprocess.run(['git', '-C', '/Users/dominic/ZK', 'show', f'research:evidence/joint-fixture11-20261026/JFm_UNCHECKED/{f}'], capture_output=True, check=True).stdout.decode()
        o = split(g('JFm_Q25Hashes.lean.txt')); bad = [f for f, t in o.items() if g(f) != t]
        print('split25 check:', len(o), 'files,', len(bad), 'differ', bad[:3]); assert not bad
    else:
        o = split(Path(sys.argv[1]).read_text())
        for f, t in o.items(): (Path(sys.argv[2]) / f).write_text(t)
