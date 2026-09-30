#!/usr/bin/env python3
"""Same source: reuse host evidence, enforce unchanged SBF frame/runtime gates."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r97_profile' in m")
source=source.replace("fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]", """fixtures=[Path(x['path'])for x in m['r85_native']['fixtures']]
for f,x in zip(fixtures,m['r85_native']['fixtures']):assert sha(f/'proof-1.bin')==x['sha256']""")
start=source.index("    env.update(RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache))")
end=source.index("elif a.mode=='sbf':",start)
source=source[:start]+'''    control=Path(m['r97_profile']['control']);cm=json.loads((control/'r18-stage.json').read_text())
    assert [n for n,h in m['files'].items()if cm['files'].get(n)!=h]==['docs/research/v8-no-work-100-20260907/experiments/performance-sbf/Cargo.toml']
    pins={}
    for f in (control/'r24-host-a').iterdir():
        if f.is_file()and f.suffix in ['.json','.log']:
            if f.name not in ['resources.json','environment.json']:shutil.copy2(f,out/f.name);pins[f.name]=sha(f)
    shutil.copytree(control/'r24-host-a/wire-controls',out/'wire-controls')
    (out/'host-reuse.json').write_text(json.dumps({'replayed':False,'log_pins':pins,
      'control_manifest_sha256':sha(control/'r18-stage.json'),
      'reason':'Only SBF optimization level changed; host source and profile identical.'},indent=2)+'\\n')
'''+source[end:]
source=source.replace("'new_profile':True,","'new_profile':False,'profile_control':m['r97_profile']['control'],")
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
