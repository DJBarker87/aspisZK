#!/usr/bin/env python3
"""Sequential private SBF builds; each child build owns a capped scope."""
import subprocess
for mode,attempt in [('devnet','2'),('pool','1')]:
 subprocess.run(['ssh','dombarker@100.108.41.90','python3','/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023/build-host.py',mode,attempt],check=True)
