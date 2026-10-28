from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
paths=[R/'alloc/src/fmt.rs',R/'alloc/src/string.rs',R/'core/src/fmt/mod.rs',R/'std/src/io/error.rs',R/'std/src/sys/pal/unix/os.rs',R/'std/src/sys/pal/unix/mod.rs',R/'backtrace/src/symbolize/gimli/elf.rs']
paths+=list((R/'std/src').rglob('*.rs'))
paths+=list((R/'backtrace').rglob('line.rs'))
rows=[]
for p in dict.fromkeys(paths):
 if not p.exists():continue
 raw=p.read_bytes();ls=raw.decode().splitlines();hits=[i for i,s in enumerate(ls) if 'from_utf8_lossy' in s or 'fn error_string' in s or 'fn errno_string' in s]
 if hits or p in paths[:7]:rows.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),excerpts=[dict(line=i+1,text=ls[max(0,i-8):i+12]) for i in hits]))
(D/'diagnostic-source-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
print('diagnostic files',len(rows))
