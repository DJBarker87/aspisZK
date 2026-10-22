#!/usr/bin/env python3
"""One focused native regression, one ELF set, one changed-fixture measurement."""
from pathlib import Path
import os,subprocess,sys
R=Path(__file__).resolve().parents[2]
(R/'source-revision.txt').write_text(sys.argv[1]+'\n')
runner=R/'tools/ct-kernels-20261022/run-host.py'
for name,cmd,expected in [
 ('v2-pole-native-final',['cargo','test','--release','--manifest-path','tools/ct-kernels-20261022/Cargo.toml','pole_full_shape','--','--nocapture'],'Optimized compilation then full-shape trace replay; no elimination'),
 ('v2-pole-regression-lib',['cargo','test','--release','--lib','-p','aspis-r1-cost-probe','--features','optimized-terminal,ct-host-prover','no_pole_is_lean','--','--test-threads=1','--nocapture'],'Optimized compilation then existing transfer/withdrawal exhaustive pole regression; no full proof generation or checker elimination')]:
 if len(sys.argv)>2 and sys.argv[2]=='remaining' and name=='v2-pole-native-final':continue
 subprocess.run(['python3',str(runner),name,*cmd],cwd=R,env=dict(os.environ,CT_EXPECTED=expected),check=True)
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/elf-host.py'),'v2final'],cwd=R,check=True)
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/stage-fixture-host.py'),'v2'],cwd=R,check=True)
