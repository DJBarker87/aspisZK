#!/usr/bin/env python3
"""Check source/excerpt/receipt consistency without compiling or rerunning Lean."""
import hashlib
import json
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
P = ROOT / 'docs/research/v8-r0-zk-20261009/lean'
FILES = ['R0Z/FsStatement.lean', 'R0Z/HvzkS.lean', 'R1Z/RomObserverBin.lean',
         'R1Z/ProverCommitDeployedFuel22.lean', 'R1Z/PrivacyR1HeadlineDeployed.lean',
         'R1Z/ProverCommitFuelJoin22.lean', 'R1Z/PrivacyR1HeadlineDeployedReal.lean']
def statement(s):
    start = s.index('theorem privacy_headline_deployed\n')
    return s[start:s.index(' := by', start)] + '\n'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    old = (P / FILES[3]).read_text()
    new = (P / FILES[-1]).read_text()
    assert (HERE/'before.lean.txt').read_text() == statement(old)
    assert (HERE/'after.lean.txt').read_text() == statement(new)
    report = (HERE.parent/'PRIVACY-RESTATE-20261023.md').read_text()
    assert statement(old) in report and statement(new) in report
    # Original endpoint files stay byte-identical to the initial audited revision.
    historical = '235da438aa136271c0380b2f8f2acf57203ea032'
    for f in FILES[:-1]:
        path = str((P/f).relative_to(ROOT))
        before = subprocess.check_output(['git','show',historical+':'+path],cwd=ROOT)
        assert (P/f).read_bytes() == before, f
    assert '(refinement.1 adv w hw)' in old and '(refinement.2 adv)' in old
    assert '(refinement adv w hw)' in new and 'refinement.2' not in new
    assert 'RustRealRefinement template outputs x rust observer_program := old.1' in new
    # The two numerical conclusions are identical, byte for byte.
    def numeric(s):
        start = s.index('    modelError ', s.index('theorem privacy_headline_deployed'))
        return s[start:s.index(' := by', start)]
    assert numeric(old) == numeric(new)
    # So is the complete probability-bound envelope (extra closing forall parenthesis).
    def envelope(s):
        start = s.index('      (modelError ', s.index('theorem privacy_headline_deployed'))
        return s[start:s.index(' ∧\n',start)]
    assert envelope(new) == envelope(old) + ')'
    prefix = new[:new.index('theorem privacy_headline_deployed')]
    assert 'rust.IdealRand' not in prefix
    assert '|mean (realTest h B outputs rust adv x w) -' in new
    assert 'idealTestS source (RomObserverBin.observerMap rust observer_program adv)' in new
    proof = new[new.index(' := by\n  have model'):new.index('/-- The original')]
    assert 'idealTestS rust' not in proof and 'ProverCommitObserverQueries19.ideal_bound' not in proof
    receipt = json.loads((HERE/'attempts.jsonl').read_text())
    assert receipt['source_sha256'] == sha(P/FILES[-1])
    assert receipt['exit'] == 0 and receipt['swaps'] == 0
    assert len(receipt['axioms']) == 2
    assert all(a.endswith('[propext, Classical.choice, Quot.sound]') for a in receipt['axioms'])
    dep = receipt['dependencies'][0]
    assert dep['source_sha256'] == sha(P/FILES[3])
    assert receipt['deps_fingerprint'] == hashlib.sha256(
        (dep['module']+'='+dep['object_sha256']).encode()).hexdigest()[:16]
    result = {'kind':'source/excerpt/receipt consistency; compile evidence is J10800',
              'checked_at_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              'old_endpoints_unchanged_since':historical, 'before_after_identical':False,
              'numeric_envelope_identical':True, 'lean_attempts':[10800],
              'pins':[{'path':str((P/f).relative_to(ROOT)), 'sha256':sha(P/f),
                       'bytes':(P/f).stat().st_size} for f in FILES]}
    print(json.dumps(result,indent=2))
if __name__ == '__main__':
    main()
