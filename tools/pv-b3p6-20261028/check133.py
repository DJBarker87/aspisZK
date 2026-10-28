"""Fail-closed table/body preflight; does not assert shipped/reference equality."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[2]
p=root/'evidence/pv-b3p6-20261028'
f=root/'crates/aspis-prover/src/host_forest.rs'
section=f.read_text().split('const MASK_LINKS: [(u16, u16); 136] = [',1)[1].split('];',1)[0]
pairs=[tuple(map(int,m)) for m in re.findall(r'\((\d+), (\d+)\)',section)]
assert len(pairs)==136
rows=sorted({r for pair in pairs for r in pair});assert len(rows)==214
ref=root/'tools/pv-b3p6-20261028/reference133.rs'
assert list(map(int,ref.read_text().split('    [',1)[1].split(']',1)[0].split(', ')))==rows
raw=(p/'raw133/Funs.lean').read_text();port=(p/'lean/PV_B3P_Reference133.lean').read_text()
assert re.findall(r'\b(\d+)#u16',raw)==[str(n) for n in rows]
assert port==raw.replace('import Aeneas\nimport PVB3P133.Types','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes')
assert 'def reference133.active_rows : Result (Array Std.U16 214#usize)' in raw
assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',port)
assert not re.search(r'let .*\b_\b',raw)
record=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),rows=len(rows),pairs=len(pairs),reference_sha256=hashlib.sha256(ref.read_bytes()).hexdigest(),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),root_present=True,body_port='B1 imports only',mutable_writes=0,restoration_continuations=0,shipped_equality_claim=False)
(p/'preflight133.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
