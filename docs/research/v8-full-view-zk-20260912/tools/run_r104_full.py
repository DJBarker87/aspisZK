#!/usr/bin/env python3
"""Same-proof native comparisons: no regenerated witness or challenge prefix."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r104_native' in m")
source=source.replace("fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]","fixtures=[Path(f['path'])for f in m['r104_native']['fixtures']]\nfor f,record in zip(fixtures,m['r104_native']['fixtures']):assert sha(f/'proof-1.bin')==record['sha256']")
old="    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])\n    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])"
new="""    control=Path(m['r104_native']['control']);cm=json.loads((control/'r18-stage.json').read_text())
    changed=[n for n,h in m['files'].items()if cm['files'].get(n)!=h]
    assert len(changed)==m['r104_native']['changed']
    if m['r104_native']['variant']=='aligned':
        assert len(changed)==1 and changed[0].endswith('/r103_words.rs')
        shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')
        compile('r103-word-check');run('word-check.log',[str(cache/'release/r103-word-check')])
        shutil.copy2(out/'word-check.log',out/'opening-check.log')
    else:
        assert len(changed)==4
        compile('r104-sum-check');run('sum-check.log',[str(cache/'release/r104-sum-check')])
        compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])
        shutil.copy2(control/'r24-host-a/opening-check.log',out/'opening-check.log')"""
assert source.count(old)==1;source=source.replace(old,new)
source=source.replace("        run(f'generate-world{w}.log',[str(binary),str(f)])\n",'')
source=source.replace("str(here/'check_r19_wire_controls.py')","str(here/('check_r103_wire_controls.py'if m['r104_native']['variant']=='aligned'else'check_r102_wire_controls.py'))")
source=source.replace("'new_profile':True","'new_profile':False")
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
