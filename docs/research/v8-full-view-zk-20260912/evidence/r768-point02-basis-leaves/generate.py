import hashlib, json
from pathlib import Path
root=Path('.r21-scratch/r762-point02-index-inventory/index_inventory.json')
d=json.loads(root.read_text())
inds=d['indices_by_category']['candidate_nonzero/active']+d['indices_by_category']['candidate_nonzero/inactive_nonpivot']
inds=[i for i in inds if i!=993]
assert len(inds)==99 and len(set(inds))==99
p0=[1,1,2,3,4,2,2,3,0,2]
p2=[1,1,2,3,4,2,-1,-2,0,2]
def factors(i,p):
    return [1-v if ((i>>(9-c))&1)==0 else v for c,v in enumerate(p)]
def lit(xs):
    return '['+', '.join(map(str,xs))+']'
out=Path('.r21-scratch/r768-point02-leaves')
manifest={'index_inventory_sha256':hashlib.sha256(root.read_bytes()).hexdigest(),'indices':inds,'chunks':[]}
for chunk_no,start in enumerate(range(0,len(inds),16)):
    these=inds[start:start+16]
    path=out/f'R768Point02LeavesChunk{chunk_no:02d}.UNVERIFIED.lean'
    lines=['import AspisV8R19.R750WitnessPointSupport','','namespace AspisV8R19.R768Point02LeavesChunk'+f'{chunk_no:02d}',
      'open AspisV8R16 AspisV8R17 AspisR19','open AspisR19.SourceStatementPoints','open AspisR19.R750WitnessPointSupport',
      'noncomputable section','set_option autoImplicit false','variable {F : Type*} [CommRing F]','']
    for i in these:
      for pnum,p in [(0,p0),(2,p2)]:
        fs=factors(i,p)
        lines += [f'/-- Exact source-selected ten-factor product at original index {i}, point p{pnum}. -/',
          f'theorem p{pnum}_basis_{i}_exact :',
          f'    sourcePointBasis (points (zFin10 (F := F)) {pnum}) {i} =',
          f'      ({lit(fs)} : List F).prod := by',
          f'  rw [points{pnum}_exact]',
          '  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring',
          f'#print axioms p{pnum}_basis_{i}_exact','']
    lines += ['end','end AspisV8R19.R768Point02LeavesChunk'+f'{chunk_no:02d}','']
    path.write_text('\n'.join(lines))
    manifest['chunks'].append({'path':str(path),'indices':these,'theorems':len(these)*2,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest['chunks'][0],indent=2))
