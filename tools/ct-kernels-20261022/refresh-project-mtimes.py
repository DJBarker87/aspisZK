#!/usr/bin/env python3
"""Before switching source snapshots in our private cache, invalidate owned crates.
Content hashes remain unchanged; dependencies from the registry stay cached.
This prevents an older rsync/copy mtime from incorrectly reusing a newer object.
"""
from pathlib import Path
import os,sys
r=Path(sys.argv[1]).resolve()
for base in ['crates','programs']:
 for p in (r/base).rglob('*'):
  if p.is_file() and (p.suffix=='.rs' or p.name=='Cargo.toml'):os.utime(p,None)
