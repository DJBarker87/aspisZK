from pathlib import Path
import hashlib,re,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028';p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';s=p.read_text()
blanket=re.findall(r'zeroize\.Zeroize\.Blanket\s+([A-Za-z0-9_.]+)',s)
assert blanket and set(blanket)=={'U8.Insts.ZeroizeDefaultIsZeroes'},set(blanket)
lengths=re.findall(r'Array\.Insts\.ZeroizeZeroize\s+(\d+)#usize',s)
assert set(lengths)=={'32','64'},set(lengths)
markers=[]
for i,line in enumerate(s.splitlines(),1):
 if re.search(r'(Usize|U64)\.Insts\.ZeroizeDefaultIsZeroes',line):
  assert line.startswith('def '),line
  markers.append(dict(line=i,text=line))
occurrences=[dict(line=i,text=line.strip()) for i,line in enumerate(s.splitlines(),1) if 'Array.Insts.ZeroizeZeroize' in line or 'zeroize.Zeroize.Blanket' in line]
j=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),explicit_blanket_instances=sorted(set(blanket)),array_lengths=sorted(set(map(int,lengths))),occurrences=occurrences,unused_marker_definitions=markers,boundary='Trait dictionaries are passed through extracted Zeroizing constructors/borrows. Native implicit Drop is connected by the structural Zeroizing::drop gate and ZeroDrop; no Aeneas implicit-drop execution theorem is silently inferred.',ok=True)
(E/'ZEROIZE-INSTANTIATIONS.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS emitted zeroize dictionaries: primitive u8; array lengths 32/64; other markers only definitions')
