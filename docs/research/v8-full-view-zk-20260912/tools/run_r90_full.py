#!/usr/bin/env python3
"""Current-caller shared gamma, independent source tests, complete SBF gate."""
from pathlib import Path
source=Path(__file__).with_name('run_r85_full.py').read_text()
source=source.replace("and 'r85_native' in m", "and 'r85_native' in m and 'r90_gamma' in m")
source=source.replace("'profile_control':m['r85_native']['control']", "'profile_control':m['r90_gamma']['control']")
needle="exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))"
assert source.count(needle)==1
source=source.replace(needle,"""source=source.replace(\"if m['r85_native']['variant']=='quotient':\",\"if True:\")
source=source.replace(\"control=Path(m['r85_native']['control'])\",\"control=Path(m['r90_gamma']['control'])\")
source=source.replace('Ordinary kernel and checker unchanged by quotient-only experiment.',
    'Ordinary kernel and checker unchanged by shared-gamma preparation experiment.')
source=source.replace(\"    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])\",\"\"\"
    compile('r90-gamma-check');run('gamma-check.log',[str(cache/'release/r90-gamma-check')])
    control=Path(m['r90_gamma']['control'])
    for name in ['query_arithmetic.rs','quotient_fold.rs','r55_opening_check.rs']:
        assert sha(ex/name)==sha(control/'docs/research/v8-no-work-100-20260907/experiments'/name)
    shutil.copy2(control/'r24-host-a/opening-check.log',out/'opening-check.log')
    (out/'opening-reuse.json').write_text(json.dumps({'replayed':False,'control_manifest_sha256':sha(control/'r18-stage.json')})+'\\\\n')\"\"\")
"""+needle)
exec(compile(source,str(Path(__file__).with_name('run_r85_full.py')),'exec'))
