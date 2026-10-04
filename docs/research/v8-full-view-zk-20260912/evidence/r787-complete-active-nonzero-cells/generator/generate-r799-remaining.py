#!/usr/bin/env python3
"""Render supported R787 source-cell chunks; literals are copied, never computed."""
from __future__ import annotations
import json,re,pathlib,hashlib,argparse,sys
ROOT=pathlib.Path(__file__).resolve().parent
SUPPORT=ROOT.parent/'r787-selected-support-preflight'/'support-check.json'
COVER=ROOT/'schedule-coverage.json'
OUT=ROOT/'generated'
PREF={(28,1,114),(27,2,114),(29,0,116),(60,0,243),(127,2,257),(254,2,1022)}
CHUNK_SIZE=16

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def cert_modules(reqs): return sorted(set(x[2] for x in reqs))
def lemma(req): return req[1]
def cellname(c): return f"cell_d{c['d']}_s{c['s']}_row{c['row_code']}_col{c['column_position']}"
def proof(c):
 d,s,row,val=c['d'],c['s'],c['row_code'],c['limb']; hi=4*d+s+1;lo=4*d;pw=s+1
 lines=[f'''theorem {cellname(c)} :
    sourceChord halfSelected (direction alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) {row} = ({val} : M) := by
  change sourceChord halfSelected
      (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r - qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r)
      (7 : M) (5 : M) (-5 : M) {row} = ({val} : M)
  have hdiff := sourceChord_difference halfSelected
      (qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9)) (qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) (1 : M) {row}
  have hfun : (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r - qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r) =
      (fun r => qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) r - (1 : M) * qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9) r) := by
    funext r
    simp
  rw [hfun, hdiff]
  have hlow : sourceChord halfSelected (qPair alphaSelected 0 (\u27e8{s}, by decide\u27e9)) (7 : M) (5 : M) (-5 : M) {row} = 0 := by
    simpa [alphaSelected] using
      (sourceChord_low_pair_zero halfSelected (7 : M) (5 : M) (-5 : M) alphaSelected \u27e80, by decide\u27e9 \u27e8{s}, by decide\u27e9 {row} (by decide))
  rw [hlow]
  simp only [mul_zero, sub_zero]
  have hq : qPair alphaSelected (\u27e8{d}, by decide\u27e9) (\u27e8{s}, by decide\u27e9) =
      (fun r => unitVector {hi} r - alphaSelected^{pw} * unitVector {lo} r) := by
    funext r
    simp [qPair, alphaSelected]
  rw [hq]
  have hdiff2 := sourceChord_difference halfSelected (unitVector {hi}) (unitVector {lo}) (7 : M) (5 : M) (-5 : M) (alphaSelected^{pw}) {row}
  rw [hdiff2]''']
 for u in [hi,lo]:
  k='odd' if u%2 else 'even'; j=u//2
  lines.append(f'  rw [sourceChord_unit_{k}_sourceGather halfSelected {j} {row} (by decide) (7 : M) (5 : M) (-5 : M)]')
 # Deduplicate exact same named schedules preserving first position.
 seen=set()
 for typ,j,mod in c['requirements']:
  name=('gatherGather' if typ=='gg' else 'gather')+str(j)
  if name not in seen: lines.append(f'  rw [{name}]');seen.add(name)
 lines += ['  simp only [unitVector, if_true, if_false, mul_zero, zero_add, add_zero]','  decide',f'#print axioms {cellname(c)}','']
 return '\n'.join(lines)
def render_chunk(i,cells):
 mods=sorted({m for c in cells for m in cert_modules(c['requirements'])})
 imports=['AspisV8R19.R738JointObservationModel','AspisV8R19.R773LowActiveKernel','AspisV8R19.R775GatherUnitChordBridge']+['AspisV8R19.'+m for m in mods]+['Mathlib.Data.ZMod.Basic']
 opens=['AspisV8R17','AspisV8R19.R738JointObservationModel','AspisV8R19.R773LowActiveKernel','AspisV8R19.R775GatherUnitChordBridge']+['AspisV8R19.'+m for m in mods]
 name=f'R799ActiveSourceCellsChunk{i:02d}'
 hdr='\n'.join('import '+x for x in imports)+f'''\n\nset_option autoImplicit false
namespace AspisV8R19.{name}
'''+''.join('open '+x+'\n' for x in opens)+'''noncomputable section
abbrev M := ZMod 2147483647
def alphaSelected : M := 7
def halfSelected : M := 1073741824

'''
 return hdr+'\n'.join(proof(c) for c in cells)+f'end\nend AspisV8R19.{name}\n',{'module':name,'cells':cells,'imports':imports}
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--chunk',type=int,default=0);ns=a.parse_args()
 cov=json.loads(COVER.read_text()); done=json.loads((ROOT/'compiled-coordinate-inventory.json').read_text()); completed={(x['d'],x['s'],x['row_code']) for x in done['unique_coordinates']}; cells=[c for c in cov['covered'] if (c['d'],c['s'],c['row_code']) not in PREF | completed]
 groups=[cells[i:i+CHUNK_SIZE] for i in range(0,len(cells),CHUNK_SIZE)]
 if ns.chunk>=len(groups): raise SystemExit('chunk out of range')
 text,meta=render_chunk(ns.chunk,groups[ns.chunk]); out=OUT/(meta['module']+'.lean');mf=OUT/(meta['module']+'.json'); man={'support_sha256':sha(SUPPORT),'coverage_sha256':sha(COVER),'renderer_sha256':sha(pathlib.Path(__file__)),'chunk':ns.chunk,'cell_count':len(groups[ns.chunk]),**meta}
 js=json.dumps(man,sort_keys=True,indent=2)+'\n'
 if ns.check:
  if out.exists() and mf.exists() and out.read_text()==text and mf.read_text()==js: print('check OK');return
  print('mismatch',file=sys.stderr);raise SystemExit(1)
 out.write_text(text);mf.write_text(js);print(out)
if __name__=='__main__':main()
