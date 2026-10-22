#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_target(name):
    m=json.loads((ROOT/'manifest.json').read_text())[name]
    src=ROOT/m['source']; prof=ROOT/m['profile']
    rec=json.loads((ROOT/m['launch_receipt']).read_text())
    pre=json.loads((ROOT/m['preflight']).read_text())
    cmd=json.loads((ROOT/m['launch_command']).read_text())
    closure=json.loads((ROOT/m['closure']).read_text())
    log=(ROOT/m['lean_raw_log']).read_text()
    assert sha(src)==m['source_sha256']==rec['source_sha256']==pre['source_sha256']
    assert sha(prof)==pre['profile_sha256']
    assert rec['exit_status']==0 and rec['object_sha256']==m['external_object_sha256']
    assert rec['process_swaps']==0 and rec['watchdog_abort'] is None
    assert rec['source_revision_at_launch']==pre['source_revision']
    assert cmd['argv'][-1].endswith(Path(m['source']).name)
    assert not closure['missing'] and closure['modules']==len(closure['owners'])
    assert pre['direct_imports']
    for module, owner in pre['direct_imports'].items():
        op=Path(owner['path'])
        assert op.is_file() and sha(op)==owner['sha256'], f'direct import pin changed: {module}'
    for module, owner in closure['owners'].items():
        op=Path(owner['path'])
        assert op.is_file() and sha(op)==owner['sha256'], f'closure owner changed: {module}'
    for decl, axioms in m['theorems'].items():
        match=re.search(re.escape("'"+decl+"' depends on axioms:")+r'([^\n]*(?:\n\s+[^\n]*){0,3})',log)
        assert match, f'missing #print axioms for {decl}'
        ax=match.group(1)
        assert all(a in ax for a in axioms), (decl,ax)
        assert 'sorryAx' not in ax
    assert not list((ROOT/name).rglob('*.olean')), f'compiled object included for {name}'

manifest=json.loads((ROOT/'manifest.json').read_text())
for target in ('prefix','terms'):
    verify_target(target)
assert manifest['prefix']['external_object_sha256']=='669738a769db5d5f08be177e75995352dbb46f89b9afeb14886c559fd996698a'
assert manifest['terms']['external_object_sha256']=='ea83608d633b255e62a46a9d1d38e8a695b9ee4bbaf9b867a3bba438ffcf816d'
assert manifest['terms']['depends_on']['S9CandidateBodyPrefixV1']['sha256']==manifest['prefix']['external_object_sha256']
assert not list(ROOT.rglob('*.olean')), 'packet must be source-only'
print('PASS: prefix and terms proofs, exact owner closures, receipts, axioms, and source-only packaging verified')
