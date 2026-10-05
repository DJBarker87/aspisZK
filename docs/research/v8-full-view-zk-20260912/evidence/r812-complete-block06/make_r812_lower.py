import json,pathlib
root=pathlib.Path('.');p=json.load(open(root/'.r21-scratch/r806-point02-selected-cells/PLAN.json'))['entries']
def nm(e):return f"{e['point']}_d{e['d']:03d}_s{e['s']}_flat{e['flat_position']:02d}"
for point,pnum in [('p2',2),('p0',0)]:
 es=sorted([e for e in p if e['point']==point and 0<=e['flat_position']<35],key=lambda x:x['flat_position']);caps=point.upper(); vals=','.join(str(e['selected_position']) for e in es)
 s=['import AspisV8R19.R807SourceBlock01Binding',*[f'import AspisV8R19.R812{caps}StaticLowChunk{i:02d}' for i in range(5)],'import Mathlib.Tactic.FinCases','set_option autoImplicit false','set_option maxRecDepth 32768',f'namespace AspisV8R19.R812BlockSix{caps}LowerZeros','open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R724BlockOrderMaps',*[f'open AspisV8R19.R812SourceBlock06{caps}StaticLowChunk{i:02d}' for i in range(5)],'noncomputable section',f'def lowerColumns : Fin 35 → Fin 222 := ![{vals}]', 'theorem lower_columns_exact : (fun j : Fin 35 => colOrder (⟨j.val, by omega⟩ : Fin 222)) = lowerColumns := by funext j; fin_cases j <;> rfl',f'theorem source_{point}_lower_zero (j : Fin 35) : fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition {pnum}) (lowerColumns j) = 0 := by','  fin_cases j']
 for e in es:s += [f'  · simpa [lowerColumns] using static_{nm(e)}']
 s += [f'#print axioms source_{point}_lower_zero','end',f'end AspisV8R19.R812BlockSix{caps}LowerZeros','']
 (root/f'.r21-scratch/R812BlockSix{caps}LowerZeros.lean').write_text('\n'.join(s))
