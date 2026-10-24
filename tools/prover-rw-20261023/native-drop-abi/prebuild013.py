from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-drop-abi/backend/base/src/PrePasses.ml')
s=p.read_text(); assert s.count('TAdt (TAdtId id, g)')==1
p.write_text(s.replace('TAdt (TAdtId id, g)','TAdt {id=TAdtId id; generics=g}'))
