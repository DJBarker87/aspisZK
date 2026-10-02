from pathlib import Path
import hashlib
HERE=Path(__file__).resolve().parent/'pinned-charon-source'
dest=Path(__file__).resolve().parent/'workspace-source-excerpts.txt'
files={
 'Cargo.toml':[(30,65)],
 'src/lib.rs':[(60,74)],
 'src/export.rs':[(1,28),(75,169)],
 'src/ast/krate.rs':[(220,302)],
 'src/transform/ctx.rs':[(1,28),(108,135)],
 'src/transform/mod.rs':[(78,170),(235,250),(283,330)],
 'src/options.rs':[(65,102),(695,730)],
 'src/bin/charon/main.rs':[(53,105),(168,244)],
 'src/bin/charon/cli.rs':[(1,78)],
 'src/bin/charon/ui_test.rs':[(1,110)],
 'src/bin/charon-driver/main.rs':[(48,102)],
 'src/bin/charon-driver/translate/translate_crate.rs':[(955,1015)],
}
out=[]
for rel,ranges in files.items():
 p=HERE/rel; lines=p.read_text().splitlines()
 out += [f'## {rel}',f'SHA256: {hashlib.sha256(p.read_bytes()).hexdigest()}','']
 for a,b in ranges:
  out.append(f'### Lines {a}-{b}')
  out.extend(f'{i}: {lines[i-1]}' for i in range(a,min(b,len(lines))+1))
  out.append('')
dest.write_text('\n'.join(out)+'\n')
