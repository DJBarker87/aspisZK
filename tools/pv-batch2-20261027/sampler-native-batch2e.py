from pathlib import Path
import subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
raise SystemExit(subprocess.run(['cargo','run','--manifest-path',str(H/'batch2e-sampler-native/Cargo.toml'),'--release','--offline','-j','4'],cwd=H/'candidate/src').returncode)
