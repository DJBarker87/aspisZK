"""Small literal certificates for immutable source table fields; no field arithmetic.
Each leaf reduces at most sixteen small records, never a recurrence or field term.
"""
from pathlib import Path
import re,json,hashlib,subprocess
D=Path('evidence/pv-b3q2-20261031'); O=D/'lean'
p=Path('tools/pv-b3p6-20261028/v244/host_copy_terminal_constants.rs');s=p.read_text()
shipped='crates/aspis-r1-cost-probe/src/host_copy_terminal_constants.rs'
assert subprocess.check_output(['git','show','HEAD:'+shipped])==p.read_bytes()
masks=list(map(int,re.search(r'const ACTIVE_ROW_MASKS:.*?= \[(.*?)\];',s).group(1).split(',')))
patterns=[list(map(int,m.split(',')))for m in re.findall(r'columns: \[([^]]+)\]',s)]
links=[]
for line in s.splitlines():
 if 'CompiledPoolV1PairForestLink {'not in line:continue
 kind=int(re.search(r'weight_kind: (\d+)',line)[1]);level=int(re.search(r'weight_level: (\d+)',line)[1])
 eps=[list(map(int,t))for t in re.findall(r'Endpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}',line)]
 assert len(eps)==2
 links.append((kind,level,eps))
assert (len(masks),len(patterns),len(links))==(64,14,136)
header='''import PV_B3Q_PanicGuards
namespace PV_B3Q_FrozenTables
set_option autoImplicit false
abbrev Endpoint := Nat × Nat × Nat
abbrev Link := Nat × Nat × Endpoint × Endpoint
def endpointSafe (e : Endpoint) : Bool := decide (e.1 < 1024 ∧ e.2.1 < 2 ∧ e.2.2 < 14)
def linkSafe (l : Link) : Bool := decide (l.1 < 5 ∧ l.2.1 < 64) && endpointSafe l.2.2.1 && endpointSafe l.2.2.2
def maskSafe (m : Nat) : Bool := decide (m = 6144 ∨ m = 6145 ∨ m = 4097 ∨ m = 2048 ∨ m = 2049 ∨ m = 26214 ∨ m = 1749)
end PV_B3Q_FrozenTables
'''
(O/'PV_B3Q_TableTypes.lean').write_text(header)
modules=[]
for ix,start in enumerate(range(0,136,16)):
 name=f'PV_B3Q_LinkTable{ix}';modules.append(name)
 rows=[]
 for k,l,eps in links[start:start+16]:
  a,b=eps;rows.append(f'({k},{l},({a[0]},{a[1]},{a[2]}),({b[0]},{b[1]},{b[2]}))')
 text=f'import PV_B3Q_TableTypes\nnamespace PV_B3Q_FrozenTables\ndef links{ix} : List Link := ['+',\n'.join(rows)+']\n'
 text+=f'theorem links{ix}_safe : links{ix}.all linkSafe = true := by decide\n#print axioms links{ix}_safe\nend PV_B3Q_FrozenTables\n'
 (O/(name+'.lean')).write_text(text)
name='PV_B3Q_PatternTable';modules.append(name)
t='import PV_B3Q_TableTypes\nnamespace PV_B3Q_FrozenTables\n'
for ix,rows in enumerate(patterns):
 t+=f'def columns{ix} : List Nat := {rows}\ntheorem columns{ix}_safe : columns{ix}.all (fun n => decide (n < 16)) = true := by decide\n#print axioms columns{ix}_safe\n'
for ix,start in enumerate(range(0,64,16)):
 t+=f'def masks{ix} : List Nat := {masks[start:start+16]}\ntheorem masks{ix}_safe : masks{ix}.all maskSafe = true := by decide\n#print axioms masks{ix}_safe\n'
t+='end PV_B3Q_FrozenTables\n';(O/(name+'.lean')).write_text(t)
x=dict(source=shipped,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),owned=str(p),byte_identical=True,counts=dict(patterns=14,columns=224,links=136,endpoints=272,masks=64),modules=modules,limit='Only immutable table guards. Not a complete runtime call-cone proof.',generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(D/'table-provenance.json').write_text(json.dumps(x,indent=2)+'\n')
