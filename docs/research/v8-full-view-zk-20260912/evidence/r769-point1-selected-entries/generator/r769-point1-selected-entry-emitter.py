#!/usr/bin/env python3
"""Format fixed-witness selected point-1 entry proofs from saved literals.

This generator never performs field arithmetic.  It reads the R746 direction
inventory and saved raw-row limbs, matches directions by their recorded raw
(d, s+1) header, and emits a four-existing-pointWeight rewrite proof.
"""
from pathlib import Path
import hashlib, json

ROOT=Path('.').resolve()
PLAN=ROOT/'.r21-scratch/r748-chosen222-point1-leaf-plan.json'
RAW=ROOT/'.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/matrix.raw.tsv'
OUT=ROOT/'.r21-scratch/r769-point1-selected-entry-generated'
RAW_SHA='91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af'


def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def raw_data():
    lines=RAW.read_text().splitlines()
    if sha(RAW)!=RAW_SHA: raise SystemExit('raw matrix checksum mismatch')
    cols={}
    column_records=[]
    point=None
    for line in lines:
        fields=line.split('\t')
        if len(fields)==4 and fields[0]=='column':
            column_records.append((int(fields[1]),int(fields[2]),int(fields[3])))
            cols[(int(fields[2]),int(fields[3]))]=int(fields[1])
        elif len(fields)>3 and fields[:3]==['row','215','point_1']:
            point=fields[3:]
    if point is None or len(column_records)!=242 or len(point)!=242 or len(cols) < 220:
        raise SystemExit(f'unexpected saved raw matrix shape: records={len(column_records)} unique={len(cols)} point={0 if point is None else len(point)}')
    return cols,point,column_records

IMPORTS='''import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R760PointWeightPrototype
import AspisV8R19.R760PointWeightChunk00
import AspisV8R19.R760PointWeightChunk01
import AspisV8R19.R760PointWeightChunk02
import AspisV8R19.R760PointWeightChunk03
import AspisV8R19.R760PointWeightChunk04
import AspisV8R19.R760PointWeightChunk05
import AspisV8R19.R760PointWeightChunk06
import AspisV8R19.R760PointWeightChunk07
import AspisV8R19.R760PointWeightChunk08
import AspisV8R19.R760PointWeightChunk09
import AspisV8R19.R760PointWeightChunk10

open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R760PointWeightPrototype
open AspisV8R19.R760PointWeightChunk00 AspisV8R19.R760PointWeightChunk01
open AspisV8R19.R760PointWeightChunk02 AspisV8R19.R760PointWeightChunk03
open AspisV8R19.R760PointWeightChunk04 AspisV8R19.R760PointWeightChunk05
open AspisV8R19.R760PointWeightChunk06 AspisV8R19.R760PointWeightChunk07
open AspisV8R19.R760PointWeightChunk08 AspisV8R19.R760PointWeightChunk09
open AspisV8R19.R760PointWeightChunk10
noncomputable section
set_option autoImplicit false
'''

def render(chunk, entries):
    out=[IMPORTS, f'namespace AspisV8R19.R769Point1SelectedChunk{chunk:02d}\n', 'abbrev M := ZMod 2147483647\n']
    for e in entries:
        d,s,rcol,value=e['d'],e['s'],e['raw_column'],e['value']
        n1,n2=4*d+s+1,4*d
        def pw_name(n):
            # R748 supplied these four historic names; R760 uses four-digit
            # names for every other planned pointWeight value, including 1/2.
            return {0:'pw0',3:'pw3',188:'pw188',191:'pw191'}.get(n, f'pw_{n:04d}')
        out.append(f'''/-- Saved raw matrix SHA-256 {RAW_SHA}: point_1 row 215, raw column {rcol} (direction ({d},{s+1})). -/
theorem point1_d{d:03d}_s{s} :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z {d} {s}
      (.inr (.inl 1)) = {value} := by
  unfold sparseObservation
  change (pw {n1} - 7^({s}+1)*pw {n2}) - (pw {s+1} - 7^({s}+1)*pw 0) = {value}
  rw [{pw_name(n1)}, {pw_name(n2)}, {pw_name(s+1)}, pw0]
  decide
#print axioms point1_d{d:03d}_s{s}
''')
    out.append(f'end AspisV8R19.R769Point1SelectedChunk{chunk:02d}\n')
    return ''.join(out)

def planned():
    plan=json.loads(PLAN.read_text())
    cols,row,column_records=raw_data()
    out=[]
    skipped=[]
    for plan_index,(d,s,kind) in enumerate(plan['selected_columns']['directions']):
        # R746's Fin3 slot is zero-based; the saved Rust matrix labels slots 1..3.
        raw_pair=(d,s+1)
        matches=[column for column,d0,s0 in column_records if (d0,s0)==raw_pair]
        if not matches: raise SystemExit(f'missing raw column {raw_pair}')
        # The saved raw diagnostic deliberately has seven duplicate low pairs.
        # R746 core entries are the initial selected core columns.
        raw_col=matches[0] if kind == 'core' else matches[-1]
        limb=row[raw_col].split(',')
        if limb[1:]!=['0','0','0']: raise SystemExit(f'non-M31 value at {raw_pair}: {limb}')
        entry={'plan_index':plan_index,'d':d,'s':s,'kind':kind,'raw_column':raw_col,'value':int(limb[0]),
               'pointweight_indices':[4*d+s+1,4*d,s+1,0]}
        if (d,s) in {(47,2),(127,2)}:
            skipped.append(entry)
        else: out.append(entry)
    if len(out)!=220 or len(skipped)!=2: raise SystemExit('unexpected selected direction count')
    return plan,out,skipped

def main(check=False):
    plan,entries,skipped=planned()
    chunks=[entries[i:i+32] for i in range(0,len(entries),32)]
    files={f'R769Point1SelectedChunk{i:02d}.lean':render(i,c) for i,c in enumerate(chunks)}
    manifest={
      'schema':'r769-selected-point1-entry-v1',
      'scope':'literal formatting from the pinned saved raw point_1 row; no field computation, elimination, rank, source execution, or security claim',
      'raw_matrix':{'path':str(RAW.relative_to(ROOT)),'sha256':sha(RAW),'row':215,'label':'point_1'},
      'selected_column_plan':{'path':str(PLAN.relative_to(ROOT)),'sha256':sha(PLAN),'total':222,'reused_existing':skipped,'generated_count':len(entries)},
      'mapping_convention':'R746 Fin3 slot s maps to raw-matrix slot s+1.',
      'chunks':[{'file':name,'entries':chunk,'sha256':hashlib.sha256(files[name].encode()).hexdigest()} for name,chunk in zip(files,chunks)],
      'source_sha256':{'emitter':sha(Path(__file__)),'R748':'06dafa57a87f421dff2014f34f5f809cebf2cd418958e582b137451a43fe7276'},
      'boundary':'Each emitted target is one fixed source-shaped algebraic witness entry. It does not prove matrix rank, universal image coverage, native execution, privacy, or security.'
    }
    targets={**files,'MANIFEST.json':json.dumps(manifest,indent=2,sort_keys=True)+'\n'}
    if check:
      for name,text in targets.items():
        p=OUT/name
        if not p.is_file() or p.read_text()!=text: raise SystemExit(f'mismatch: {p}')
      print('check ok',len(entries),'generated entries; skipped',[(x['d'],x['s']) for x in skipped])
      return
    OUT.mkdir(parents=True,exist_ok=True)
    for name,text in targets.items(): (OUT/name).write_text(text)
    print(OUT)

if __name__=='__main__':
    import sys
    main('--check' in sys.argv)
