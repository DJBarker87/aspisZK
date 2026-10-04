#!/usr/bin/env python3
"""Render bounded literal-source row equalities from pinned R787/R800 metadata.
No field values are computed: each RHS literal is copied from coordinate metadata.
"""
import argparse,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
E=pathlib.Path('docs/research/v8-full-view-zk-20260912/evidence/r787-complete-active-nonzero-cells')
MAP=E/'COORDINATE_THEOREM_MAP.json'; SUPPORT=E/'inputs/support-check.json'; OUT=ROOT/'generated'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def name(code):return f'literalRow{code}'
def emit_def(code,cells):
 expr='0'
 for c in reversed(cells): expr=f'if j.val = {c["column_position"]} then {c["first_limb"]} else {expr}'
 return f'def {name(code)} (j : Fin 222) : M := {expr}\n'
def emit_row(code,activeidx,cells,zero_module):
 cases=[]
 for n,c in enumerate(cells):
  h=f'h{n}';pos=c['column_position'];d=c['d'];s=c['s'];v=c['first_limb'];mod=c['module'];th=c['theorem']
  # Earlier false conditions only; all later RHS branches are simplifier-normalized.
  earlier=', '.join(f'h{i}' for i in range(n))
  simp_args=f'[{name(code)}, {earlier}]' if earlier else f'[{name(code)}]'
  cases.append(f'''  by_cases {h} : j.val = {pos}
  · have hj : j = (⟨{pos}, by decide⟩ : Fin 222) := Fin.ext {h}
    subst j
    simp {simp_args}
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨{d}, by decide⟩) (⟨{s}, by decide⟩))
      (7 : M) (5 : M) (-5 : M) {code} = ({v} : M)
    exact {mod}.{th}
''')
 # terminal outside support: explicit list nonmembership is discharged only from the branch inequalities.
 hs=', '.join(f'h{i}' for i in range(len(cells)))
 listlit='['+', '.join(str(c['column_position']) for c in cells)+']'
 zero=f'{zero_module}.row{code}_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j'
 if len(cells) == 1:
  terminal=f'''  · simp [{name(code)}, {hs}]
    rw [literalSourceMatrix_active_entry]
    apply {zero}
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
'''
 else:
  branches=' | '.join('hbad' for _ in cells)
  rejects='\n'.join(f'    · exact h{i} hbad' for i in range(len(cells)))
  terminal=f'''  · simp [{name(code)}, {hs}]
    rw [literalSourceMatrix_active_entry]
    apply {zero}
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with {branches}
{rejects}
'''
 cases.append(terminal)
 # all selected active row supports are normally 1-5; generic terminal omega based on hypotheses.
 proof=''.join(cases)
 return f'''theorem literalSourceMatrix_row{code} :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨{activeidx}, by decide⟩ : Fin 214)) = {name(code)} := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
{proof}#print axioms literalSourceMatrix_row{code}
'''
def render_group(n,rows,coord):
 imports=['AspisV8R19.R804LiteralSourceRow114','AspisV8R19.R801LiteralActiveEntries','AspisV8R19.R799LiteralSourceMatrix','AspisV8R19.R748JointWitnessPointEntry','Mathlib.Data.ZMod.Basic']
 zero=f'AspisV8R19.R800SelectedSupportChunk{n:02d}'
 imports.append(zero)
 for r in rows:
  for p in r['support_columns']:
   c=coord[(r['row_code'],p)];imports.append(c['module'])
 imports=sorted(set(imports))
 mod=f'R804LiteralSourceRowsChunk{n:02d}'
 hdr='\n'.join('import '+x for x in imports)+f'''\n\nset_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.{mod}
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
'''
 body=''
 for r in rows:
  code=r['row_code']; cells=[coord[(code,p)] for p in r['support_columns']]; idx=ROWS.index(r)
  body+=emit_def(code,cells)+'\n'+emit_row(code,idx,cells,zero)+'\n'
 return mod,hdr+body+f'end\nend AspisV8R19.{mod}\n'
def render_1022(coord):
 code=1022; r=next(r for r in ROWS if r['row_code']==code); c=coord[(code,212)]
 mod='R804LiteralSourceRow1022';imports=['AspisV8R19.R804LiteralSourceRow114','AspisV8R19.R801LiteralActiveEntries','AspisV8R19.R799LiteralSourceMatrix','AspisV8R19.R800SelectedSupportPrototype','AspisV8R19.R778ActiveEntryPrototype','AspisV8R19.R748JointWitnessPointEntry','Mathlib.Data.ZMod.Basic']
 hdr='\n'.join('import '+x for x in imports)+f'''\n\nset_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.{mod}
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R800SelectedSupportPrototype
noncomputable section
abbrev M := ZMod 2147483647
'''
 idx=ROWS.index(r);v=c['first_limb']
 body=f'''def literalRow1022 (j : Fin 222) : M := if j.val = 212 then {v} else 0
theorem literalSourceMatrix_row1022 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected kappaSelected tauSelected z)
      (activePosition (⟨{idx}, by decide⟩ : Fin 214)) = literalRow1022 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h : j.val = 212
  · have hj : j = (⟨212, by decide⟩ : Fin 222) := Fin.ext h
    subst j
    simp [literalRow1022]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨254, by decide⟩) (⟨2, by decide⟩)) (7:M) (5:M) (-5:M) 1022 = ({v}:M)
    exact AspisV8R19.R778ActiveEntryPrototype.active_entry_raw_column_212_row_code_1022
  · simp [literalRow1022,h]
    rw [literalSourceMatrix_active_entry]
    exact AspisV8R19.R800SelectedSupportPrototype.row1022_source_zero halfSelected alphaSelected (7:M) (5:M) (-5:M) j (by simpa using h)
#print axioms literalSourceMatrix_row1022
end
end AspisV8R19.{mod}
'''
 return mod,hdr+body
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
 global ROWS
 sup=json.loads(SUPPORT.read_text());ROWS=sup['rows']; mp=json.loads(MAP.read_text())['entries'];coord={(x['row_code'],x['column_position']):x for x in mp}
 assert len(ROWS)==214 and len(coord)==700
 remaining=[r for r in ROWS if r['row_code'] not in (114,1022)];groups=[remaining[i:i+4] for i in range(0,len(remaining),4)];assert len(groups)==53
 outputs=[]
 for n,g in enumerate(groups):
  mod,text=render_group(n,g,coord);outputs.append((OUT/(mod+'.lean'),text))
 mod,text=render_1022(coord);outputs.append((OUT/(mod+'.lean'),text))
 if a.check:
  for p,t in outputs:
   if not p.exists() or p.read_text()!=t:raise SystemExit('mismatch '+str(p))
  print('check OK',len(outputs),'files');return
 OUT.mkdir(parents=True,exist_ok=True)
 for p,t in outputs:p.write_text(t)
 manifest={'map_sha256':sha(MAP),'support_sha256':sha(SUPPORT),'files':[str(p) for p,_ in outputs],'rows':214,'reused_row114':True,'separate_row1022':True}
 (ROOT/'all-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('wrote',len(outputs))
if __name__=='__main__':main()
