#!/usr/bin/env python3
"""Same-profile experiments: preserve R84 proof bytes, run changed source gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r85_native' in m")
old="fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]"
new="""fixtures=[Path(x['path'])for x in m['r85_native']['fixtures']]
for f,x in zip(fixtures,m['r85_native']['fixtures']):assert sha(f/'proof-1.bin')==x['sha256']"""
assert source.count(old)==1;source=source.replace(old,new)
old="        run(f'generate-world{w}.log',[str(binary),str(f)])"
assert source.count(old)==1;source=source.replace(old,'        # Exact existing proofs: do not rerun witness/proof generation.')
source=source.replace("'new_profile':True,","'new_profile':False,'profile_control':m['r85_native']['control'],")
old="    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])"
new="""    if m['r85_native']['variant']=='quotient':
        control=Path(m['r85_native']['control'])
        reused=control/'r24-host-a/compact-check.log'
        assert 'compact_source_implemented=true' in reused.read_text()
        shutil.copy2(reused,out/'compact-check.log')
        (out/'compact-reuse.json').write_text(json.dumps({'replayed':False,'log_sha256':sha(reused),
            'control_manifest_sha256':sha(control/'r18-stage.json'),'reason':'Ordinary kernel and checker unchanged by quotient-only experiment.'},indent=2)+'\\n')
    else:
        compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
