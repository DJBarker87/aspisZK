#!/usr/bin/env python3
import pathlib,re,json,hashlib
root=pathlib.Path('.')
lean=root/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19'
out=root/'.r21-scratch/r812-block06-binding/generated'; out.mkdir(parents=True,exist_ok=True)
r801=(lean/'R801LiteralActiveEntries.lean').read_text()
segment=r801.split('def activeCodes : List Nat := [',1)[1].split(']',1)[0]
codes=[int(x) for x in re.findall(r'\d+',segment)]
# Block 6 positions 0..36 are active rows.  The source active position is
# rowOrder (flatIndex 6 local), not the local block coordinate.
rowmap_src=(lean/'R724BlockOrderMaps.lean').read_text()
rowseg=rowmap_src.split('def rowOrder',1)[1].split('def rowOrderInv',1)[0]
rowmap={int(i):int(v) for i,v in re.findall(r'\| (\d+) => (\d+)', rowseg)}
def active_pos(local):
    return rowmap[35+local]  # blockOffset 6 is the pinned literal 35
# local row 0 is already green in R812SourceBlock06Binding.
locals_=list(range(1,37))
assert len(locals_)==36
# exact source module for each literal theorem
mapping={}
for p in lean.glob('R804LiteralSourceRow*.lean'):
 t=p.read_text()
 for x in re.findall(r'theorem literalSourceMatrix_row(\d+)\b',t):mapping[int(x)]=p.stem
for li in locals_:
 assert codes[active_pos(li)] in mapping,(li,active_pos(li),codes[active_pos(li)])

def render(chunk, items):
 mods=sorted({mapping[codes[active_pos(i)]] for i in items})
 lines=['import AspisV8R19.R807SourceBlock01Binding','import AspisV8R19.R747JointBlock39Preflight','import AspisV8R19.R804LiteralSourceRow114',*[f'import AspisV8R19.{m}' for m in mods],'','set_option autoImplicit false','set_option maxRecDepth 32768',f'namespace AspisV8R19.R812SourceBlock06RowsChunk{chunk:02d}','open AspisV8R19.R807SourceBlock01Binding','open AspisV8R19.R806LiteralBlockLayout','open AspisV8R19.R724BlockOrderMaps','open AspisV8R19.R799LiteralSourceMatrix','open AspisV8R19.R801LiteralActiveEntries','open AspisV8R19.R804LiteralSourceRow114','open AspisV8R19.R748JointWitnessPointEntry',*[f'open AspisV8R19.{m}' for m in mods],'noncomputable section','abbrev M := ZMod 2147483647','local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩','']
 for local in items:
  pos=active_pos(local); code=codes[pos]; theorem=f'literalSourceMatrix_row{code}'
  lines += [f'''theorem source_block06_active_row_local{local:02d} (j : Fin 39) :
    diagonalSourceBlock 6 (⟨{local}, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨{local}, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨{local}, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨{pos}, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨{pos},by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [{theorem}]
  revert j
  decide
#print axioms source_block06_active_row_local{local:02d}
''']
 lines += ['end','end AspisV8R19.R812SourceBlock06RowsChunk%02d'%chunk,'']
 return '\n'.join(lines)
files={}
for n in range((len(locals_)+3)//4):
 x=locals_[4*n:4*n+4]; files[f'R812SourceBlock06RowsChunk{n:02d}.lean']=render(n,x)
for k,v in files.items():(out/k).write_text(v)
man={'active_local_indices':locals_,'active_positions':{str(i):active_pos(i) for i in locals_},'active_codes':{str(i):codes[active_pos(i)] for i in locals_},'literal_source_modules':{str(i):mapping[codes[active_pos(i)]] for i in locals_},'files':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in files.items()}}
(out/'MANIFEST.json').write_text(json.dumps(man,indent=2)+'\n')
