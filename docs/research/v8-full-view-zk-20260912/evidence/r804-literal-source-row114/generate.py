#!/usr/bin/env python3
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
MAP=pathlib.Path('docs/research/v8-full-view-zk-20260912/evidence/r787-complete-active-nonzero-cells/COORDINATE_THEOREM_MAP.json')
OUT=ROOT/'R804LiteralSourceRow114.UNVERIFIED.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 d=json.loads(MAP.read_text()); entries=[x for x in d['entries'] if x['row_code']==114]
 assert {(x['column_position'],x['first_limb']) for x in entries}=={(0,2147483409),(220,1342177280)}
 s='''import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R797ActiveSourceCellsPreflight
import AspisV8R19.R748JointWitnessPointEntry
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRow114
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R800SelectedSupportPrototype
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R797ActiveSourceCellsPreflight
noncomputable section
abbrev M := ZMod 2147483647
def halfSelected : M := 1073741824
def quarterSelected : M := 536870912
def alphaSelected : M := 7
def uSelected : M := 2
def vSelected : M := 3
def kappaSelected : M := 5
def tauSelected : M := 0
def literalRow114 (j : Fin 222) : M :=
  if j.val = 0 then 2147483409 else if j.val = 220 then 1342177280 else 0

theorem literalSourceMatrix_row114 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (\u27e80, by decide\u27e9 : Fin 214)) = literalRow114 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 0
  · have hj : j = (\u27e80, by decide\u27e9 : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow114]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (\u27e828, by decide\u27e9) (\u27e81, by decide\u27e9))
      (7 : M) (5 : M) (-5 : M) 114 = (2147483409 : M)
    exact cell_d28_s1_row114
  · by_cases h220 : j.val = 220
    · have hj : j = (\u27e8220, by decide\u27e9 : Fin 222) := Fin.ext h220
      subst j
      simp [literalRow114, h0]
      rw [literalSourceMatrix_active_entry]
      change sourceChord halfSelected (direction alphaSelected (\u27e827, by decide\u27e9) (\u27e82, by decide\u27e9))
        (7 : M) (5 : M) (-5 : M) 114 = (1342177280 : M)
      exact cell_d27_s2_row114
    · simp [literalRow114, h0, h220]
      rw [literalSourceMatrix_active_entry]
      exact row114_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j (by simpa using And.intro h0 h220)

#print axioms literalSourceMatrix_row114
end
end AspisV8R19.R804LiteralSourceRow114
'''
 OUT.write_text(s)
 (ROOT/'manifest.json').write_text(json.dumps({'coordinate_map_sha256':sha(MAP),'cells':entries,'output_sha256':sha(OUT)},indent=2)+'\n')
 print(OUT)
if __name__=='__main__':main()
