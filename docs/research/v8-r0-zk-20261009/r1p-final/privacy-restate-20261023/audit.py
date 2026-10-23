#!/usr/bin/env python3
"""Read-only source audit; no Lean compilation or theorem certification."""
import hashlib
import json
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
P = ROOT / 'docs/research/v8-r0-zk-20261009/lean'
FILES = ['R0Z/FsStatement.lean', 'R0Z/HvzkS.lean', 'R1Z/RomObserverBin.lean',
         'R1Z/ProverCommitDeployedFuel22.lean', 'R1Z/PrivacyR1HeadlineDeployed.lean',
         'R1Z/ProverCommitFuelJoin22.lean']
def statement(s):
    start = s.index('theorem privacy_headline_deployed\n')
    end = s.index(' := by', start)
    return s[start:end] + '\n'
def main():
    s = (P / FILES[3]).read_text()
    before = statement(s)
    for name in ['before.lean.txt', 'after.lean.txt']:
        assert (HERE / name).read_text() == before, name
    assert '(refinement.1 adv w hw)' in s and '(refinement.2 adv)' in s
    fs = (P / FILES[0]).read_text()
    hv = (P / FILES[1]).read_text()
    assert 'ideal : (Challenges K → Tape K F → View K CommitHandle Aux Bat)' in fs
    assert 'fun r => bit (fs.observe adv (fs.ideal sim adv x r))' in hv
    result = {'kind': 'source inspection only; no new theorem',
              'inspected_revision': '235da438aa136271c0380b2f8f2acf57203ea032',
              'checked_at_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'endpoint_unchanged': True, 'before_after_identical': True,
              'lean_attempts': [], 'axioms': None,
              'pins': [{'path': str((P / f).relative_to(ROOT)),
                        'sha256': hashlib.sha256((P / f).read_bytes()).hexdigest(),
                        'bytes': (P / f).stat().st_size} for f in FILES]}
    print(json.dumps(result, indent=2))
if __name__ == '__main__':
    main()
