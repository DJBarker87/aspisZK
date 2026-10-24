"""Only adapt the emitted constant shift-count numeral to the pinned backend API."""
from pathlib import Path
import hashlib,json,sys
src,dst,receipt=map(Path,sys.argv[1:]); s=src.read_text()
a='Std.U64.wrapping_shl remainder 32#i32';b='Std.U64.wrapping_shl remainder 32#u32'
assert s.count(a)==1
out=s.replace(a,b);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(out)
receipt.write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),replacement=[a,b],count=1,qualification='Explicit backend numeral compatibility adaptation. No Rust change; output is not the unmodified emitted file. Wrapping/checked semantics require separate checked theorems.'),indent=2)+'\n')
