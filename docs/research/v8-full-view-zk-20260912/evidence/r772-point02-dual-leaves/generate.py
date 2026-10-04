import hashlib, json, sys
from pathlib import Path
invp=Path('.r21-scratch/r762-point02-index-inventory/index_inventory.json')
d=json.loads(invp.read_text())
idx=d['indices_by_category']
zeros=idx['source_basis_zero/inactive_nonpivot']+idx['source_basis_zero/active']
cands=idx['candidate_nonzero/active']+idx['candidate_nonzero/inactive_nonpivot']
assert len(zeros)==419 and len(cands)==100 and len(set(zeros+cands))==519
allidx=zeros+cands
assert len(set(allidx))==519
# The separately checked R772 prototype covers these exact two originals for both points.
prototype={14,780}
assert prototype <= set(allidx)
remaining=[i for i in allidx if i not in prototype]
assert len(remaining)==517
p0=[1,1,2,3,4,2,2,3,0,2]
p2=[1,1,2,3,4,2,-1,-2,0,2]
def fs(i,p): return [1-v if ((i>>(9-c))&1)==0 else v for c,v in enumerate(p)]
def list_lit(xs): return '['+', '.join(map(str,xs))+']'
# point-to-exact-basis dependency source
candidate_module={}
# R768 filtered prototype index 993 before dividing the remaining candidates into chunks.
filtered_cands=[i for i in cands if i!=993]
assert len(filtered_cands)==99
for chunk_no,start in enumerate(range(0,99,16)):
  for i in filtered_cands[start:start+16]: candidate_module[i]=(f'AspisV8R19.R768Point02LeavesChunk{chunk_no:02d}',f'p0_basis_{i}_exact',f'p2_basis_{i}_exact')
candidate_module[993]=('AspisV8R19.R768Point02BasisLeaves','p0_basis_993_exact','p2_basis_993_exact')
# Confirm every candidate resolves to a green R768 source theorem.
assert set(candidate_module)==set(cands)
out=Path('.r21-scratch/r772-point02-dual-leaves')
manifest={'inventory_sha256':hashlib.sha256(invp.read_bytes()).hexdigest(),'prototype_indices_reused':sorted(prototype),'zero_original_count':len(zeros),'candidate_original_count':len(cands),'total_original_count':len(allidx),'remaining_originals_in_chunks':remaining,'chunks':[]}
baseimports=['AspisV8R19.R772Point02DualLeaves','AspisV8R19.R750WitnessPointSupport','AspisV8R19.R752SharedWitnessPointSupport']
# Import each R768 block containing a candidate. They are cached products of prior green focused runs.
baseimports += [f'AspisV8R19.R768Point02LeavesChunk{i:02d}' for i in range(7)]
baseimports += ['AspisV8R19.R768Point02BasisLeaves']
for cn,start in enumerate(range(0,len(remaining),16)):
  these=remaining[start:start+16]
  path=out/f'R772Point02DualLeavesChunk{cn:02d}.UNVERIFIED.lean'
  nsp=f'R772Point02DualLeavesChunk{cn:02d}'
  lines=[*(f'import {x}' for x in baseimports),'',f'namespace AspisV8R19.{nsp}',
    'open AspisV8R16 AspisV8R17 AspisR19','open AspisR19.R750WitnessPointSupport','open AspisR19.TwoSwapSourceTable',
    'noncomputable section','set_option autoImplicit false','variable {F : Type*} [CommRing F]','']
  for i in these:
    iszero=i in set(zeros)
    for pn in [0,2]:
      pts=f'AspisV8R19.R771Point02Transport.point{pn} (F := F)'
      th=f'p{pn}_transport_'+('zero' if iszero else 'exact')+f'_original_{i}'
      lines += [f'/-- Transport at original index {i}, point p{pn}. -/',f'theorem {th} :',
        f'    AspisV8R16.transportDual inactive (1023 : Fin 1024) order',
        f'      (fun k : Fin 1024 => sourcePointBasis ({pts}) k.val)',
        f'      (order.symm ({i} : Fin 1024)) =']
      if iszero:
        lines += ['      0 := by',f'  rw [AspisV8R19.R772Point02DualLeaves.point{pn}_transport_original]',
          (f'  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) {i} (by decide)' if pn==0 else f'  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) {i} (by decide)'),
          f'#print axioms {th}','']
      else:
        mod,t0,t2=candidate_module[i]
        basisth=t0 if pn==0 else t2
        lines += [f'      ({list_lit(fs(i,p0 if pn==0 else p2))} : List F).prod := by',
          f'  rw [AspisV8R19.R772Point02DualLeaves.point{pn}_transport_original]',
          f'  simpa [AspisV8R19.R771Point02Transport.point{pn}] using {mod}.{basisth} (F := F)',
          f'#print axioms {th}','']
  lines += ['end','end AspisV8R19.'+nsp,'']
  generated='\n'.join(lines)
  if '--check' in sys.argv:
    assert path.is_file() and path.read_text()==generated, f'generated source mismatch: {path}'
    generated_sha=hashlib.sha256(generated.encode()).hexdigest()
  else:
    path.write_text(generated)
    generated_sha=hashlib.sha256(path.read_bytes()).hexdigest()
  manifest['chunks'].append({'path':str(path),'original_indices':these,'theorem_count':2*len(these),'sha256':generated_sha})
manifest_text=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:
  mp=out/'manifest.json'
  assert mp.is_file() and mp.read_text()==manifest_text, f'manifest mismatch: {mp}'
else:
  (out/'manifest.json').write_text(manifest_text)
print('R772 generator check OK' if '--check' in sys.argv else json.dumps(manifest['chunks'][0],indent=2))
