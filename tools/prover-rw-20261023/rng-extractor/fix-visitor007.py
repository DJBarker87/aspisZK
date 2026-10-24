from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/base/src/Main.ml')
s=p.read_text();assert s.count('inherit [_] iter_ty as super')==1
s=s.replace('inherit [_] iter_ty as super','inherit [_] Types.iter_ty as super').replace('| TRef _ -> unsupported', '| Types.TRef _ -> unsupported')
p.write_text(s)
