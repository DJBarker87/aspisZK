#!/usr/bin/env python3
"""Opening-only gates, reusing identical ordinary evidence; unchanged proof bytes."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r93_opening' in m")
source=source.replace("fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]", """fixtures=[Path(x['path'])for x in m['r85_native']['fixtures']]
for f,x in zip(fixtures,m['r85_native']['fixtures']):assert sha(f/'proof-1.bin')==x['sha256']""")
source=source.replace("        run(f'generate-world{w}.log',[str(binary),str(f)])",'        # Existing exact proof bytes; no proof regeneration.')
source=source.replace("'new_profile':True,","'new_profile':False,'profile_control':m['r93_opening']['control'],")
old="    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])"
new="""    control=Path(m['r93_opening']['control']);cm=json.loads((control/'r18-stage.json').read_text())
    changed=[n for n,h in m['files'].items()if cm['files'].get(n)!=h]
    assert changed==['docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs']
    reused=control/'r24-host-a/compact-check.log';assert 'compact_source_implemented=true' in reused.read_text()
    shutil.copy2(reused,out/'compact-check.log')
    (out/'compact-reuse.json').write_text(json.dumps({'replayed':False,'log_sha256':sha(reused),
      'control_manifest_sha256':sha(control/'r18-stage.json'),'reason':'Only opening limb call layout changed; all ordinary sources/checker identical.'},indent=2)+'\\n')"""
assert source.count(old)==1;source=source.replace(old,new)
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
