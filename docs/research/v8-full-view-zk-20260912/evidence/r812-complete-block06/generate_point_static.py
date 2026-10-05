import json,pathlib,re,hashlib
root=pathlib.Path('.'); lean=root/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19'
plan=json.load(open(root/'.r21-scratch/r806-point02-selected-cells/PLAN.json'))['entries']
mod={}
for p in lean.glob('R806Point02SelectedChunk*.lean'):
 for n in re.findall(r'theorem (p[02]_d\d+_s\d+_flat\d+)\b',p.read_text()):mod[n]=p.stem
def nm(e):return f"{e['point']}_d{e['d']:03d}_s{e['s']}_flat{e['flat_position']:02d}"
def render(point,ci,es):
 used=sorted({mod[nm(e)] for e in es}); ns=f'AspisV8R19.R812SourceBlock06{point.upper()}StaticChunk{ci:02d}'
 lines=['import AspisV8R19.R807SourceBlock01Binding','import AspisV8R19.R803LiteralSupplementaryEntries',*[f'import AspisV8R19.{x}' for x in used],'set_option autoImplicit false','set_option maxRecDepth 32768',f'namespace {ns}','open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding',*[f'open AspisV8R19.{x}' for x in used],'noncomputable section','local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩','']
 pnum=0 if point=='p0' else 2
 for e in es:
  t=f'static_{nm(e)}'; val=e['first_limb']; sp=e['selected_position']
  lines += [f'theorem {t} : fixedSourceMatrix (pointPosition {pnum}) (⟨{sp},by decide⟩ : Fin 222) = {val} := by','  unfold fixedSourceMatrix','  rw [literalSourceMatrix_point_entry]',f'  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z {e["d"]} {e["s"]} (.inr (.inl {pnum})) = {val}',f'  exact {nm(e)}',f'#print axioms {t}','']
 lines += ['end',f'end {ns}','']
 return '\n'.join(lines),used
out=root/'.r21-scratch/r812-block06-binding/point-static';out.mkdir(parents=True,exist_ok=True); manifest={}
for point in ['p0','p2']:
 es=[e for e in plan if e['point']==point and 35<=e['flat_position']<=73]
 for ci in range((len(es)+7)//8):
  part=es[ci*8:(ci+1)*8];txt,used=render(point,ci,part);fn=f'R812SourceBlock06{point.upper()}StaticChunk{ci:02d}.lean';(out/fn).write_text(txt);manifest[fn]={'sha256':hashlib.sha256(txt.encode()).hexdigest(),'entries':[nm(e) for e in part],'imports':used}
(out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
