from pathlib import Path
import sys,re
R=Path(__file__).resolve().parents[2]
raw=(R/'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs').read_text()
links=[tuple(map(int,m)) for m in re.findall(r'CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}',raw)]
assert len(links)==136
O=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for c in range(4):
 name=f'PV_Inv_MaskChunk{c}'
 s=f'import R1Z.PV_Inv_MaskPartition\nset_option autoImplicit false\nnamespace R1Z.{name}\nopen R0P\n'
 for b in range(c*16,c*16+16):
  s+=f'theorem block_{b} : PV_Inv_MaskSource.mask {b} = copyActiveRowMasks {b} := by\n'
  if b>=51:
   for n in range(34):
    v=0
    for a in links[4*n:4*n+4]:
     for r in (a[3],a[6]):
      if r//16==b:v|=1<<(r%16)
    s+=f'  have c{n:02} : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk{n:02}.links {b} = {v} := by rfl\n'
   s+='  rw [PV_Inv_MaskPartition.decomposition,'+','.join(f'c{n:02}' for n in range(34))+']\n  rfl\n'
  else:s+='  rw [PV_Inv_MaskPartition.decomposition]\n  rfl\n'
  s+=f'#print axioms block_{b}\n'
 s+=f'end R1Z.{name}\n'
 p=(Path(__file__).parent/'pending'/(name+'.lean.txt')) if c==3 else O/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
