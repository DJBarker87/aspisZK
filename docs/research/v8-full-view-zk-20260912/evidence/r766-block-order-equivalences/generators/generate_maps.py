#!/usr/bin/env python3
"""Generate literal Fin 222 block permutations and their inverse tables from pinned R724 metadata."""
from pathlib import Path
import argparse,hashlib,json,re

ROOT=Path(__file__).resolve().parents[2]
INV=ROOT/'.r21-scratch/r724-block-permutation-inventory/index_inventory.json'
INV_SHA='268e05932211ba21ebdb9d774a58e53f38ed21ef42dc417da8b6d866b175a48e'
CERT_SHA='d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4'
RAW_SHA='91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af'
OUT=Path(__file__).resolve().parent/'generated'
CHUNK=32


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def emit_match(name,values):
    branches='\n'.join(f'  | {i} => {v}' for i,v in enumerate(values))
    return f'def {name} (i : Fin 222) : Fin 222 :=\n  match i.val with\n{branches}\n  | _ => 0\n'

def emit_index_fact(kind, direction, n):
    maps={
        ('row','left'):('rowOrderInv','rowOrder'),
        ('row','right'):('rowOrder','rowOrderInv'),
        ('col','left'):('colOrderInv','colOrder'),
        ('col','right'):('colOrder','colOrderInv'),
    }
    outer,inner=maps[(kind,direction)]
    name=f'{kind}Order_{direction}_{n:03d}'
    return f'theorem {name} : {outer} ({inner} ({n} : Fin 222)) = {n} := by decide\n#print axioms {name}\n'

def build():
    if sha(INV)!=INV_SHA: raise SystemExit('pinned R724 index inventory checksum mismatch')
    d=json.loads(INV.read_text())
    if d['certificate_sha256']!=CERT_SHA or d['raw_matrix_sha256']!=RAW_SHA: raise SystemExit('pinned R724 certificate/raw checksum mismatch')
    row=d['flattened_row_original_ids']
    rowinv=d['original_row_to_flat_position_inverse']
    col=d['flattened_column_minor_positions']
    colinv=d['minor_column_to_flat_position_inverse']
    for label,xs in [('rowOrder',row),('rowOrderInv',rowinv),('colOrder',col),('colOrderInv',colinv)]:
        if len(xs)!=222 or sorted(xs)!=list(range(222)): raise SystemExit(f'{label} not a literal Fin 222 permutation')
    if [rowinv[x] for x in row]!=list(range(222)): raise SystemExit('row inverse metadata mismatch')
    if [colinv[x] for x in col]!=list(range(222)): raise SystemExit('column inverse metadata mismatch')
    src='''/-! Literal SCC-block position maps derived from the pinned R724 metadata.
    Rows map flat block positions to original row IDs. Columns map flat block
    positions to selected-minor column positions, after `selected_columns⁻¹`.
    This file makes no matrix-entry, inverse, rank, or verifier claim. -/
set_option autoImplicit false
namespace AspisV8R19.R724BlockOrderMaps

'''+emit_match('rowOrder',row)+'\n'+emit_match('rowOrderInv',rowinv)+'\n'+emit_match('colOrder',col)+'\n'+emit_match('colOrderInv',colinv)+'\nend AspisV8R19.R724BlockOrderMaps\n'
    case='''import AspisV8R19.R724BlockOrderMaps
/-! First bounded index-only round-trip cases for the pinned block maps. -/
set_option autoImplicit false
namespace AspisV8R19.R724BlockOrderCase0
open AspisV8R19.R724BlockOrderMaps

theorem rowOrder_inverse_at_zero : rowOrderInv (rowOrder 0) = 0 := by decide
#print axioms rowOrder_inverse_at_zero

theorem colOrder_inverse_at_zero : colOrderInv (colOrder 0) = 0 := by decide
#print axioms colOrder_inverse_at_zero
end AspisV8R19.R724BlockOrderCase0
'''
    chunks=[]
    for chunk_id, lo in enumerate(range(0,222,CHUNK)):
        hi=min(222,lo+CHUNK)
        chunksrc=f'''import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R724BlockOrderCase0
/-! Literal scalar round-trip facts for indices {lo} through {hi-1}.
    These are index-table facts only; they say nothing about matrix entries. -/
set_option autoImplicit false
namespace AspisV8R19.R724BlockOrderChunk{chunk_id:02d}
open AspisV8R19.R724BlockOrderMaps
'''
        for n in range(lo,hi):
            for kind,direction in [('row','left'),('row','right'),('col','left'),('col','right')]:
                if n==0 and (kind,direction) in {('row','left'),('col','left')}:
                    continue
                chunksrc+='\n'+emit_index_fact(kind,direction,n)
        chunksrc+=f'\nend AspisV8R19.R724BlockOrderChunk{chunk_id:02d}\n'
        chunks.append((f'R724BlockOrderChunk{chunk_id:02d}.lean',chunksrc))
    outputs=[('R724BlockOrderMaps.lean',src),('R724BlockOrderCase0.lean',case),*chunks]
    manifest={'schema':'r724-block-order-maps-v2','index_inventory_sha256':sha(INV),'certificate_sha256':CERT_SHA,'raw_matrix_sha256':RAW_SHA,'dimensions':{'Fin222':222,'blocks':len(d['blocks'])},'chunk_indices':CHUNK,'map_semantics':{'rowOrder':'flattened rows_original: flat block position -> original row id','rowOrderInv':'original row id -> flat block position','colOrder':'flattened columns_original mapped through selected_columns inverse: flat block position -> minor column position','colOrderInv':'minor column position -> flat position'},'first_cases':{'rowOrder_0':row[0],'rowOrder_inverse_at_zero':'rowOrderInv (rowOrder 0) = 0','colOrder_0':col[0],'colOrder_inverse_at_zero':'colOrderInv (colOrder 0) = 0'},'reused_facts':['rowOrder_left_000','colOrder_left_000'],'chunks':{n:hashlib.sha256(body.encode()).hexdigest() for n,body in chunks},'outputs':{n:hashlib.sha256(body.encode()).hexdigest() for n,body in outputs}}
    return outputs,manifest

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    outputs,manifest=build(); OUT.mkdir(parents=True,exist_ok=True)
    mt=json.dumps(manifest,indent=2,sort_keys=True)+'\n';stale=[]
    expected={n for n,_ in outputs};actual={p.name for p in OUT.glob('*.lean')}
    if a.check and (expected!=actual): stale.append(f'lean files mismatch extras={sorted(actual-expected)} missing={sorted(expected-actual)}')
    for name,body in outputs:
        p=OUT/name
        if a.check:
            if not p.exists() or p.read_text()!=body: stale.append(name)
        else:p.write_text(body)
    m=OUT/'manifest.json'
    if a.check:
        if not m.exists() or m.read_text()!=mt:stale.append('manifest.json')
        if stale:raise SystemExit('stale/missing: '+', '.join(stale))
        print('--check: pinned index metadata and literal sources match')
    else:
        m.write_text(mt);print(json.dumps(manifest['first_cases'],sort_keys=True));print(f'wrote {len(outputs)} sources')
if __name__=='__main__':main()
