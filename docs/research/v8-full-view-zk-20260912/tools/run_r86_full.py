#!/usr/bin/env python3
"""Run changed Merkle gates and complete execution on the exact R84 proofs."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r86_native' in m")
old="fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]"
new="""fixtures=[Path(x['path'])for x in m['r85_native']['fixtures']]
for f,x in zip(fixtures,m['r85_native']['fixtures']):assert sha(f/'proof-1.bin')==x['sha256']"""
assert source.count(old)==1;source=source.replace(old,new)
old="        run(f'generate-world{w}.log',[str(binary),str(f)])"
assert source.count(old)==1;source=source.replace(old,'        # No regeneration: exact pinned proof bytes.')
source=source.replace("'new_profile':True,","'new_profile':False,'profile_control':m['r86_native']['control'],")
old="""    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])
    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])"""
new="""    control=Path(m['r86_native']['control'])
    reused=[]
    for name in ['compact-check.log','opening-check.log']:
        path=control/'r24-host-a'/name
        assert 'Exit status: 0' in path.read_text()
        shutil.copy2(path,out/name)
        reused.append({'path':str(path),'sha256':sha(path)})
    (out/'arithmetic-reuse.json').write_text(json.dumps({'replayed':False,'logs':reused,
        'reason':'Neither arithmetic kernel nor its checker changes in the Merkle overlay.'},indent=2)+'\\n')
    prior=Path('/home/dombarker/project-offloads/aspis-r20-r86-merkle-20260929-a')
    for name in ['crates/aspis-core/src/v7_merkle208.rs',
        'docs/research/v8-no-work-100-20260907/experiments/merkle_input_tests.rs']:
        assert sha(prior/name)==sha(s/name)
    path=prior/'r24-host-a/merkle-source-tests.log'
    assert '4 passed; 0 failed' in path.read_text() and 'Exit status: 0' in path.read_text()
    shutil.copy2(path,out/'merkle-source-tests.log')
    (out/'merkle-reuse.json').write_text(json.dumps({'replayed':False,'path':str(path),'sha256':sha(path),
        'reason':'Exact source and tests unchanged; first run passed before unrelated old host test-harness compile failure.'},indent=2)+'\\n')
    compile('r86-leaf-check');run('leaf-source-tests.log',[str(cache/'release/r86-leaf-check')])"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
