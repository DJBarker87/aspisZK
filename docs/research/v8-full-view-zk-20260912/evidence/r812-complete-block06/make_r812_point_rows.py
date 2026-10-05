import json,pathlib
root=pathlib.Path('.');plan=json.load(open(root/'.r21-scratch/r806-point02-selected-cells/PLAN.json'))['entries']
def nm(e):return f"{e['point']}_d{e['d']:03d}_s{e['s']}_flat{e['flat_position']:02d}"
def render(point,pnum):
 es=sorted([e for e in plan if e['point']==point and 35<=e['flat_position']<=73],key=lambda e:e['flat_position']);assert len(es)==39
 caps=point.upper(); vals=','.join(map(str,[e['first_limb'] for e in es]))
 lines=['import AspisV8R19.R816BlockSixSourceView','import AspisV8R19.R813FiniteFunctionExt39',*[f'import AspisV8R19.R812{caps}StaticChunk{i:02d}' for i in range(5)],'set_option autoImplicit false',f'namespace AspisV8R19.R812BlockSix{caps}SourceRow','open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R813FiniteFunctionExt39','open AspisV8R19.R812SourceBlock06'+caps+'StaticChunk00 AspisV8R19.R812SourceBlock06'+caps+'StaticChunk01 AspisV8R19.R812SourceBlock06'+caps+'StaticChunk02 AspisV8R19.R812SourceBlock06'+caps+'StaticChunk03 AspisV8R19.R812SourceBlock06'+caps+'StaticChunk04','noncomputable section','abbrev M := R807SourceBlock01Binding.M',f'def {point}Values : Fin 39 → M := ![{vals}]',f'theorem source_{point}_values : (fun j : Fin 39 => fixedSourceMatrix (pointPosition {pnum}) (block06Columns j)) = {point}Values := by',f'  apply fin39_ext']
 for e in es:
  i=e['flat_position']-35; chunk=(i//8); t='static_'+nm(e)
  lines += [f'  · simpa [{point}Values, block06Columns] using {t}']
 lines += [f'#print axioms source_{point}_values','end',f'end AspisV8R19.R812BlockSix{caps}SourceRow','']
 return '\n'.join(lines)
for point,pnum in [('p2',2),('p0',0)]: (root/f'.r21-scratch/R812BlockSix{point.upper()}SourceRow.lean').write_text(render(point,pnum))
