#!/usr/bin/env python3
"""Emit/check bounded index-support facts for the saved 214x222 active block."""
import argparse,csv,hashlib,json,re
from pathlib import Path
BASE=Path('.')
EVID=BASE/'docs/research/v8-full-view-zk-20260912/evidence/r769-point1-selected-entries'
RAW=EVID/'inputs/matrix.raw.tsv'
MAPPING=EVID/'lead-mapping-check.json'
SUMMARY=BASE/'.r21-scratch/r778-active-matrix-sparsity-summary.json'
SUPPORT=BASE/'.r21-scratch/r787-selected-support-preflight/support-check.json'
R798=BASE/'.r21-scratch/R798LiteralObservationView.lean'
R787=BASE/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R787PairSupportZero.lean'
R800=BASE/'.r21-scratch/R800SelectedSupportPrototype.lean'
OUT=BASE/'.r21-scratch/r800-selected-support/generator-output'
PINS={
 'raw_matrix':'91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af',
 'mapping':'8b8506e8c85975f798d566d07ceeaff586b5eb12ad76aeaa58c554dc9902fa04',
 'summary':'182915860a04793e56a50cf9b8352c411840877015ff46cc480a4801b00ffeb2',
 'support':'4ddaff34fc112bc64cb5484b81c7af7e96f10301326ce3a686b39ca4f641b592',
 'R798':'6ea5f7651b1208f588a6eb29e5377318c3766fe20aa16cfd1f14cee17b048cb8',
 'R787':'b17902d251355267290c8bb5fb7e6cff7a01d2e3a1f6844a41a7881290ba7b37',
 'R800':'5822e9fb6a3fda18c7f71b0383ae5da9da4d804d5dddc2ff2baae79a1a07ceec',
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def emit_row(code,support):
    xs=', '.join(map(str,support))
    name=f'row{code}'
    return f'''theorem {name}_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 {code} ↔
      i.val ∈ ([{xs}] : List Nat) := by
  revert i
  decide

theorem {name}_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([{xs}] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c {code} = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h (({name}_support i).mp hs)

#print axioms {name}_support
#print axioms {name}_source_zero
'''
def main():
 ap=argparse.ArgumentParser(); g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--check',action='store_true');g.add_argument('--write',action='store_true');a=ap.parse_args()
 for name,p in [('raw_matrix',RAW),('mapping',MAPPING),('summary',SUMMARY),('support',SUPPORT),('R798',R798),('R787',R787),('R800',R800)]:
  got=sha(p)
  if got!=PINS[name]:raise SystemExit(f'{name} SHA mismatch {got} != {PINS[name]}')
 raw=list(csv.reader(RAW.open(),delimiter='\t')); assert raw[0]==['rows=222 columns=242']
 summary=json.loads(SUMMARY.read_text()); support=json.loads(SUPPORT.read_text()); mapping=json.loads(MAPPING.read_text())
 rows=support['rows']; assert len(rows)==214 and support['counts']['support_positive']==700
 assert support['counts']['support_positive_but_literal_zero']==0 and support['counts']['outside_support_but_literal_nonzero']==0
 assert mapping['exact_selected_columns']==support['selected_raw_columns']
 rowcodes=[x['source_rowcode'] for x in summary['raw_row_slot_to_label_and_source_rowcode']]
 assert [r['row_code'] for r in rows]==rowcodes
 assert len(raw)==465
 for i,code in enumerate(rowcodes):assert raw[243+i][2]==f'active_chord_{code}'
 labels=[f'active_chord_{c}' for c in rowcodes]+['point_0','point_1','point_2','ordinary_relation_1','ordinary_relation_2','ordinary_relation_3','ordinary_relation_5','ordinary_relation_6']
 assert [raw[243+i][2] for i in range(222)]==labels
 # Compare the generated finite columnView constructor list with the saved chosen raw headers.
 block=R798.read_text().split('def literalColumns : List (Fin 255 × Fin 3) := ',1)[1].split('\ntheorem literalColumns_length',1)[0]
 found=[(int(d),int(s)) for d,s in re.findall(r'⟨(\d+), by decide⟩,⟨(\d+), by decide⟩',block)]
 assert len(found)==222
 assert found==[tuple(x) for x in support['selected_headers_d_s']]
 # Keep the two already-green prototypes out of the new chunks.
 remaining=[r for r in rows if r['row_code'] not in (114,1022)]
 assert len(remaining)==212 and len({r['row_code'] for r in remaining})==212
 groups=[remaining[i:i+4] for i in range(0,len(remaining),4)]
 assert len(groups)==53 and max(map(len,groups))<=4
 generated=[]
 for n,group in enumerate(groups):
  mod=f'R800SelectedSupportChunk{n:02d}';path=OUT/f'{mod}.lean'
  bodies=''.join(emit_row(r['row_code'],r['support_columns']) for r in group)
  src=f'''import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.{mod}
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {{F : Type*}} [CommRing F]
{bodies}end AspisV8R19.{mod}
'''
  generated.append((path,src,group))
 expected={p for p,_,_ in generated}; existing=set(OUT.glob('R800SelectedSupportChunk*.lean'))
 if a.check:
  if existing!=expected:raise SystemExit(f'output mismatch missing={len(expected-existing)} extra={len(existing-expected)}')
  for p,s,_ in generated:
   if p.read_text()!=s:raise SystemExit(f'generated source mismatch: {p}')
  print(f'check ok: {len(generated)} chunks, 212 rows, max {max(map(len,groups))}/chunk; 114 and 1022 reused')
 else:
  OUT.mkdir(parents=True,exist_ok=True)
  for p,s,_ in generated:p.write_text(s)
  print(f'wrote {len(generated)} chunks, 212 rows, max {max(map(len,groups))}/chunk; 114 and 1022 reused')
if __name__=='__main__':main()
