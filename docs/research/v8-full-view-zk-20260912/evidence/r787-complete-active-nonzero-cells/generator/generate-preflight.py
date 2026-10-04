#!/usr/bin/env python3
"""Render the bounded first R787 active-source cell certificate module.
Values are copied from the pinned support matrix; this program does no field arithmetic.
"""
from __future__ import annotations
import argparse, hashlib, json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parent
SUPPORT=ROOT.parent/'r787-selected-support-preflight'/'support-check.json'
OUT=ROOT/'generated'/'R797ActiveSourceCellsPreflight.lean'
# Four fresh cells: s=0/1/2 and both parity branches.  R778's two published cells
# remain reused evidence and are deliberately not compiled again.
SELECT=[(28,1,114),(27,2,114),(29,0,116),(60,0,243)]
# Direct sourceGather certificate required after unit splitting.
GATHER={
 (28,1,114): [('R748GatherExpand00','gather57'),('R748GatherExpand00','gather56')],
 (27,2,114): [('R748GatherExpand00','gather55'),('R748GatherExpand00','gather54')],
 (29,0,116): [('R748GatherExpand00','gather58')],
 (60,0,243): [('R748GatherExpand02','gather120')],
}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def find_cell(data,d,s,row):
 xs=[x for x in data['literal_nonzero_positions'] if (x['d'],x['s'],x['row_code'])==(d,s,row)]
 if len(xs)!=1: raise ValueError(f'expected one support cell for {(d,s,row)}, got {len(xs)}')
 x=xs[0]
 if x['limbs'][1:] != [0,0,0]: raise ValueError(f'non-first limbs at {(d,s,row)}')
 return x

def proof(d,s,row,val):
 unit_hi=4*d+s+1; unit_lo=4*d; pow=s+1
 hi_j=unit_hi//2; lo_j=unit_lo//2
 lines=[f'''theorem cell_d{d}_s{s}_row{row} :
    sourceChord halfSelected (direction alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) {row} = ({val} : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r -
        qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r)
      (7 : M) (5 : M) (-5 : M) {row} = ({val} : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9))
      (qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) (1 : M) {row}
  have hfun : (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r -
      qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r) =
      (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r -
      (1 : M) * qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) {row} = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected
        \u27e80, by decide\u27e9 \u27e8{s}, by decide\u27e9 {row} (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) =
      (fun r => unitVector {unit_hi} r - alphaSelected^{pow} * unitVector {unit_lo} r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector {unit_hi}) (unitVector {unit_lo})
      (7 : M) (5 : M) (-5 : M) (alphaSelected^{pow}) {row}
  rw [hdiff2]''']
 for unit,j in [(unit_hi,hi_j),(unit_lo,lo_j)]:
  kind='odd' if unit%2 else 'even'
  lines.append(f'''  rw [sourceChord_unit_{kind}_sourceGather halfSelected {j} {row} (by decide)
      (7 : M) (5 : M) (-5 : M)]''')
 for _,name in GATHER[(d,s,row)]: lines.append(f'  rw [{name}]')
 lines += ['  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]', '  decide', f'#print axioms cell_d{d}_s{s}_row{row}', '']
 return '\n'.join(lines)

def render():
 data=json.loads(SUPPORT.read_text())
 cells=[find_cell(data,*x) for x in SELECT]
 imports=['AspisV8R19.R738JointObservationModel','AspisV8R19.R773LowActiveKernel','AspisV8R19.R775GatherUnitChordBridge','AspisV8R19.R748GatherExpand00','AspisV8R19.R748GatherExpand02','Mathlib.Data.ZMod.Basic']
 opens=['AspisV8R17','AspisV8R19.R738JointObservationModel','AspisV8R19.R773LowActiveKernel','AspisV8R19.R775GatherUnitChordBridge','AspisV8R19.R748GatherExpand00','AspisV8R19.R748GatherExpand02']
 top='\n'.join('import '+x for x in imports)+'''\n\nset_option autoImplicit false
namespace AspisV8R19.R797ActiveSourceCellsPreflight
open '''+'\nopen '.join(opens)+'''\nnoncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

'''
 body='\n'.join(proof(x['d'],x['s'],x['row_code'],x['limbs'][0]) for x in cells)
 return top+body+'end\nend AspisV8R19.R797ActiveSourceCellsPreflight\n', {'support_sha256':sha(SUPPORT),'raw_matrix_sha256':data['input_sha256']['raw_matrix'],'selected':cells,'schedule':[{'d': d, 's': s, 'row': row, 'certificates':[{'module':mod,'lemma':lemma} for mod,lemma in GATHER[(d,s,row)]]} for d,s,row in SELECT],'renderer':'no field arithmetic; support literals copied verbatim'}

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); a=ap.parse_args()
 text,manifest=render(); m=json.dumps(manifest,indent=2,sort_keys=True)+'\n'
 mf=ROOT/'manifest.json'
 if a.check:
  ok=OUT.exists() and mf.exists() and OUT.read_text()==text and mf.read_text()==m
  if not ok: print('generated output or manifest differs',file=sys.stderr); return 1
  print('check OK'); return 0
 OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(text); mf.write_text(m)
 print(OUT); print(mf)
if __name__=='__main__': raise SystemExit(main())
