#!/usr/bin/env python3
"""Emit/check literal observation view chunks from the pinned R769 raw mapping.
No values are evaluated; source row/column labels are checked exactly.
"""
import argparse, csv, hashlib, json, sys
from pathlib import Path
BASE=Path('.')
EVID=BASE/'docs/research/v8-full-view-zk-20260912/evidence/r769-point1-selected-entries'
RAW=EVID/'inputs/matrix.raw.tsv'
MAPPING=EVID/'lead-mapping-check.json'
SUMMARY=BASE/'.r21-scratch/r778-active-matrix-sparsity-summary.json'
R790=BASE/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R790LiteralObservationOrderPrototype.lean'
OUT=BASE/'.r21-scratch/r790-literal-observation-order/generator-output'
PINS={
 'raw_matrix':'91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af',
 'mapping':'8b8506e8c85975f798d566d07ceeaff586b5eb12ad76aeaa58c554dc9902fa04',
 'summary':'182915860a04793e56a50cf9b8352c411840877015ff46cc480a4801b00ffeb2',
 'R790':'11461f518e4026cd8203b3716221bfe9034115250105277365286b5e02f8f3e2',
}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def finpair(d,s): return f'(⟨{d}, by decide⟩, ⟨{s}, by decide⟩)'
def high_block(ix,code,d,s):
    label=f'{ix:03d}'
    return f'''def high_{label} : High := ⟨⟨{code}, by decide⟩, by decide⟩
def obs_{label} : Obs := Sum.inl (Sum.inl high_{label})
theorem row_{label}_members_highActive : (⟨{code}, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_{label}_rowCode : rowCode (Sum.inl high_{label} : High ⊕ Unit) = {code} := by decide
theorem row_{label}_selectedColumns : selectedColumns obs_{label} = {finpair(d,s)} := by decide
#print axioms row_{label}_members_highActive
#print axioms row_{label}_rowCode
#print axioms row_{label}_selectedColumns
'''
def top_block(d,s):
    return f'''def obs_top : Obs := Sum.inl (Sum.inr ())
theorem top_rowCode : rowCode (Sum.inr () : High ⊕ Unit) = 1022 := by decide
theorem top_selectedColumns : selectedColumns obs_top = {finpair(d,s)} := by decide
#print axioms top_rowCode
#print axioms top_selectedColumns
'''
def extra_block(kind,i,d,s):
    if kind=='point':
        obs=f'Sum.inr (Sum.inl (⟨{i}, by decide⟩ : Fin 3))'
    else:
        obs=f'Sum.inr (Sum.inr (⟨{i}, by decide⟩ : Fin 5))'
    name=f'{kind}_{i}'
    return f'''def obs_{name} : Obs := {obs}
theorem {name}_selectedColumns : selectedColumns obs_{name} = {finpair(d,s)} := by decide
#print axioms {name}_selectedColumns
'''

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); ap.add_argument('--write',action='store_true'); args=ap.parse_args()
    if args.check==args.write: raise SystemExit('choose exactly one of --check or --write')
    for name,p in [('raw_matrix',RAW),('mapping',MAPPING),('summary',SUMMARY),('R790',R790)]:
        got=sha(p)
        if got!=PINS[name]: raise SystemExit(f'{name} SHA mismatch: {got} != {PINS[name]}')
    tab=list(csv.reader(RAW.open(),delimiter='\t'))
    assert tab[0]==['rows=222 columns=242'] and len(tab)==465
    raw_headers={int(r[1]):(int(r[2]),int(r[3])-1) for r in tab[1:243] if len(r)==4 and r[0]=='column'}
    assert len(raw_headers)==242 and set(raw_headers)==set(range(242))
    summary=json.loads(SUMMARY.read_text())
    rowmeta=summary['raw_row_slot_to_label_and_source_rowcode']
    rowcodes=[x['source_rowcode'] for x in rowmeta]
    assert len(rowcodes)==214 and rowcodes[-1]==1022 and all(x['label']==f'active_chord_{x["source_rowcode"]}' for x in rowmeta)
    rawcols=json.loads(MAPPING.read_text())['exact_selected_columns']
    assert len(rawcols)==222 and len(set(rawcols))==222
    # The TSV's first 214 selected columns are the 213 high observations plus top unit;
    # final eight correspond to three point and five coefficient observation constructors.
    ds=[raw_headers[x] for x in rawcols]
    assert ds[213]==(254,1)
    assert ds[214:217]==[(23,0),(23,1),(23,2)]
    assert ds[217:220]==[(24,0),(24,1),(24,2)]
    assert ds[220:222]==[(27,2),(47,2)]
    # Check all raw row labels, preserving the table's actual slot ordering.
    expected_labels=[f'active_chord_{code}' for code in rowcodes]+[
        'point_0','point_1','point_2','ordinary_relation_1','ordinary_relation_2',
        'ordinary_relation_3','ordinary_relation_5','ordinary_relation_6']
    assert [tab[243+i][2] for i in range(222)]==expected_labels
    blocks=[]
    # Continue from existing canonical first eight facts; chunk size is capped at 16 new observations.
    remaining=[]
    for i,code in enumerate(rowcodes[:213]): remaining.append(('high',i,code,*ds[i]))
    remaining=remaining[8:]
    remaining.append(('top',213,1022,*ds[213]))
    for i in range(3): remaining.append(('point',i,None,*ds[214+i]))
    for i in range(5): remaining.append(('coeff',i,None,*ds[217+i]))
    # High observations are 16 per chunk; final top/supplement chunk also stays under 16.
    groups=[remaining[i:i+16] for i in range(0,len(remaining),16)]
    assert len(groups)==14 and max(map(len,groups))<=16
    for gi,group in enumerate(groups):
        mod=f'R790LiteralObservationChunk{gi:02d}'
        rel=OUT/f'{mod}.lean'
        if gi==0: imp='AspisV8R19.R790LiteralObservationOrderPrototype'
        else: imp=f'AspisV8R19.R790LiteralObservationChunk{gi-1:02d}'
        body=[]
        for kind,i,code,d,s in group:
            body.append(high_block(i,code,d,s) if kind=='high' else top_block(d,s) if kind=='top' else extra_block(kind,i,d,s))
        text=f'''import {imp}
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.{mod}
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

{''.join(body)}end AspisV8R19.{mod}
'''
        blocks.append((rel,text,group))
    expected={p for p,_,_ in blocks}
    existing={p for p in OUT.glob('R790LiteralObservationChunk*.lean')}
    if args.check:
        if existing!=expected: raise SystemExit(f'output set mismatch: missing={sorted(map(str,expected-existing))}, extra={sorted(map(str,existing-expected))}')
        for p,text,_ in blocks:
            if p.read_text()!=text: raise SystemExit(f'generated source mismatch: {p}')
        print(f'check ok: {len(blocks)} chunks; {sum(len(g) for _,_,g in blocks)} new observations; max chunk={max(len(g) for _,_,g in blocks)}')
    else:
        OUT.mkdir(parents=True,exist_ok=True)
        for p,text,_ in blocks: p.write_text(text)
        print(f'wrote {len(blocks)} chunks; {sum(len(g) for _,_,g in blocks)} new observations; max chunk={max(len(g) for _,_,g in blocks)}')
        print('input pins:',json.dumps(PINS,sort_keys=True))
if __name__=='__main__': main()
