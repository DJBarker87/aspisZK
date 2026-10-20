#!/usr/bin/env python3
from pathlib import Path
import re,hashlib,json,sys
raw=Path(sys.argv[1]); clean=Path(sys.argv[2]); name=raw.name
s=raw.read_text()
s=re.sub(r"(?m)^/\- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n\n", "", s)
s=re.sub(r"(?m)^/\- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n\n", "", s)
assert s==clean.read_text()
assert "set_option maxHeartbeats" not in s and "set_option maxRecDepth" not in s
print(name+": only Aeneas resource-setting comments/lines removed")
