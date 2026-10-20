#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
P='/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021/continuation4/bank-included-extraction/pins.json'
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+P],text=True))
checked={}
for name,sha in r['sources'].items():
    p=ROOT/name
    assert p.exists(),name
    actual=hashlib.sha256(p.read_bytes()).hexdigest()
    assert actual==sha, name
    checked[name]=actual
assert r['exit']==0
copy_names=['docs/research/v8-r0-zk-20261009/refine/'+x+'/src/lib.rs' for x in ['writers','blockwriters','poseidon']]
for name in copy_names:
    remote='/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021/source/'+name
    sha=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum '+remote],text=True).split()[0]
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==sha,name
    checked[name]=sha
(HERE/'bank-source-check.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),pins_host_path=P,sources=checked,tools=r['tools'],scope='all statement/core .rs/.toml pins in inherited extraction, plus all three copy-crate lib.rs inputs'),indent=2)+'\n')
print('PASS',len(checked),'source pins')
