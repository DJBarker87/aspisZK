from pathlib import Path
import subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
for i,m in enumerate(['OptionEquality','MatrixIntermediate','PrimitiveInspect','MatrixRawFixture0','MatrixRawFixture1','ScalarEquality','FmtInspect'],70244):
 r=subprocess.run(['python3',str(H/'serial.py'),str(i)+':PV_B3Q_'+m],cwd=H)
 if r.returncode:raise SystemExit(r.returncode)
