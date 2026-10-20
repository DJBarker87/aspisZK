#!/usr/bin/env python3
from pathlib import Path
import re,hashlib,json,sys
repo=Path(sys.argv[1]); kit=Path(sys.argv[2]); pins=json.loads((kit/"source-map.json").read_text())
err=(repo/"crates/aspis-core/src/r0/mod.rs").read_text(); opening=(repo/"crates/aspis-core/src/r0/opening.rs").read_text(); lib=(kit/"input/src/lib.rs").read_text()
mp=re.search(r"(?ms)^#\[derive\(Clone, Copy, Debug, PartialEq, Eq\)\]\npub enum Error \{.*?^\}",err).group(0)
cp=re.search(r"(?ms)^pub const COPY_ACTIVE_ROW_MASKS: \[u16; 64\] = \[.*?^];",opening).group(0)
fp=re.search(r"(?ms)^pub fn inactive\(r: usize\) -> Result<bool, Error> \{.*?^\}",opening).group(0)
assert mp in lib and cp in lib and fp in lib
for rel in ("crates/aspis-core/src/r0/mod.rs","crates/aspis-core/src/r0/opening.rs"):
 assert hashlib.sha256((repo/rel).read_bytes()).hexdigest()==pins["source_files"][rel]["sha256"]
print("exact source cut: Error enum, COPY_ACTIVE_ROW_MASKS, inactive body")
