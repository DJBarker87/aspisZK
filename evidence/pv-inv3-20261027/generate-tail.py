from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];O=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
raw=(R/'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs').read_text()
links=[tuple(map(int,m)) for m in re.findall(r'CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}',raw)]
assert len(links)==136
masks=list(map(int,re.search(r'def copyActiveRowMasks.*?!\[(.*?)\]',(R/'docs/research/v8-r0-sem-proof-20261008/lean/R0P/CopyConstants.lean').read_text()).group(1).split(',')))
for b in range(48,64):
 name=f'PV_Inv_MaskTail{b}'
 s=f'import R1Z.PV_Inv_MaskPartition\nset_option autoImplicit false\nnamespace R1Z.{name}\nopen R0P\n'
 s+=f'theorem installed_table : copyActiveRowMasks {b} = {masks[b]} := by rfl\n#print axioms installed_table\n'
 vals=[]
 for n in range(34):
  v=0
  for a in links[4*n:4*n+4]:
   for r in (a[3],a[6]):
    if r//16==b:v|=1<<(r%16)
  vals.append(v)
  s+=f'theorem contribution{n:02} : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk{n:02}.links {b} = {v} := by rfl\n#print axioms contribution{n:02}\n'
 s+=f'theorem block : PV_Inv_MaskSource.mask {b} = copyActiveRowMasks {b} := by\n  rw [installed_table,PV_Inv_MaskPartition.decomposition,'+','.join(f'contribution{n:02}' for n in range(34))+']\n  rfl\n#print axioms block\n'
 s+=f'end R1Z.{name}\n'
 p=O/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
