#!/usr/bin/env python3
"""Word encoding: actual-source affine gates before new proofs/full SBF."""
from pathlib import Path
source=Path(__file__).with_name('run_r102_full.py').read_text()
source=source.replace("and 'r102_auth' in m","and 'r103_words' in m")
source=source.replace("m['r102_auth']['control']","m['r103_words']['control']")
source=source.replace("compile('r102-auth-check');run('auth-check.log',[str(cache/'release/r102-auth-check')])",
    "compile('r103-word-check');run('word-check.log',[str(cache/'release/r103-word-check')])")
# The old r55 executable needs the new module because query_arithmetic now has
# a word entry. The new checker invokes the same retained old controls already.
source=source.replace("exec(compile(source,", "source=source.replace(\"    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])\", \"    shutil.copy2(out/'word-check.log',out/'opening-check.log')\")\nexec(compile(source,")
source=source.replace('check_r102_wire_controls.py','check_r103_wire_controls.py')
source=source.replace("exec(compile(source,", "source=source.replace(\"'--old-fixture',str(Path(m['r85_native']['fixtures'][0]['path']))\", \"'--old-fixture',str(Path(m['r103_words']['control'])/'r24-host-a/fixture-world0'),'--old-fixture',str(Path(m['r85_native']['fixtures'][0]['path']))\")\nexec(compile(source,")
exec(compile(source,str(Path(__file__).with_name('run_r102_full.py')),'exec'))
