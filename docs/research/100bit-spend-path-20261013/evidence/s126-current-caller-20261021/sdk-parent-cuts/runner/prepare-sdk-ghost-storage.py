#!/usr/bin/env python3
"""Separate harness-only mutable storage from pooled constant allocations.
Each ghost value is projected from a uniquely tagged enclosing allocation.
No source function, symbolic input, assertion, or contract is removed.
"""
from pathlib import Path
import sys,re,json,hashlib
base,out=map(Path,sys.argv[1:3]);(out/'src').mkdir(parents=True,exist_ok=False)
original=(base/'src/lib.rs').read_text();lines=original.splitlines(keepends=True)
decl=re.compile(r'^(\s*)static mut (\w+):(.+)=(.+);\s*$')
names=[decl.fullmatch(line).group(2) for line in lines if decl.fullmatch(line)]
assert names and len(names)==len(set(names))
pattern=re.compile(r'\b('+ '|'.join(names) +r')\b')
result=[];inserted=False;index=0;rows=[]
for line in lines:
 m=decl.fullmatch(line)
 if m:
  if not inserted:
   result.append(' struct GhostStorage<T> { value:T, allocation_tag:u64 }\n');inserted=True
  indent,name,typ,value=m.groups();index+=1;tag=0x51A2000000000000+index
  result.append(f'{indent}static mut {name}:GhostStorage<{typ}>=GhostStorage{{value:{value},allocation_tag:{tag}}};\n')
  rows.append(dict(name=name,type=typ,initializer=value,tag=tag))
 else:result.append(pattern.sub(lambda m:m[0]+'.value',line))
source=''.join(result)
# Projection changes only references to harness globals. The complete source
# before its cfg(kani) module is kept byte-for-byte, including observer().
prefix=original[:original.index('#[cfg(kani)] mod proofs')]
assert source.startswith(prefix)
(out/'src/lib.rs').write_text(source)
(out/'Cargo.toml').write_bytes((base/'Cargo.toml').read_bytes())
sha=lambda b:hashlib.sha256(b).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(
 schema='focused-extractor-proof-packet-v1',qualification=__doc__,
 source_sha256=sha(source.encode()),base_source_sha256=sha(original.encode()),
 unchanged_source_prefix_sha256=sha(prefix.encode()),ghost_projection=rows,
 retained_obligations='Audit raw emitted source functions and all assertions. Tagged storage addresses are ghost-only; actual SDK buffers, descriptors, aliases, child arguments and observed values retain the same domain. No native caller or release closure follows from this transformation alone.'),indent=2)+'\n')
