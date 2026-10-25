#!/usr/bin/env python3
"""Generate reader from an immutable, exact guard span; no compiler invocation."""
import hashlib,subprocess
from pathlib import Path
T=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','74a62fd7b6:tools/port29sdkdata-20261025/Port29SDKDATA_Strict-v3.lean']).decode()
a=s.index('def sameDeclaration');b=s.index('\ndef readComplete')
guard=s[a:b]
header='import Lean\nopen Lean\nnamespace Port31DATA\n-- EXACT Port29 guard span, only enclosing namespace differs.\n-- Source74a62fd7b6, span SHA256 '+hashlib.sha256(guard.encode()).hexdigest()+'\n'
(T/'Port31DATA_Raw.lean').write_text(header+guard+'\n'+(T/'Port31DATA_reader-body.lean.txt').read_text())
