import pathlib,csv,hashlib
b=pathlib.Path('docs/research/v8-full-view-zk-20260912');p=b/'evidence/r769-point1-selected-entries/inputs/matrix.raw.tsv';assert hashlib.sha256(p.read_bytes()).hexdigest()=='91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af'
tab=list(csv.reader(p.open(),delimiter='\t'));codes=[int(r[2].removeprefix('active_chord_')) for r in tab[243:457]];assert len(codes)==214
s='''import AspisV8R19.R799LiteralSourceMatrix
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R801LiteralActiveEntries
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R799LiteralSourceMatrix
noncomputable section

def activeCodes : List Nat := ['''+', '.join(map(str,codes))+''']
theorem activeCodes_length : activeCodes.length = 214 := rfl

def activeCodeView (i : Fin 214) : Nat :=
  activeCodes.get (Fin.cast activeCodes_length.symm i)

def activePosition (i : Fin 214) : Fin 222 := Fin.castLE (by decide) i

theorem activeCodeView_bounds (i : Fin 214) :
    96 ≤ activeCodeView i ∧ activeCodeView i < 1024 := by
  revert i
  decide

variable {F : Type*} [CommRing F] [Nontrivial F]
theorem literalSourceMatrix_active_entry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (i : Fin 214) (j : Fin 222) :
    literalSourceMatrix half quarter alpha u v kappa tau z (activePosition i) j =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) (activeCodeView i) := by
  rw [literalSourceMatrix_entry]
  fin_cases i
'''
for i,r in enumerate(codes):
 s+=f'''  case «{i}» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) {r} =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) {r}
    rw [rawFlatten_indexedDirection]
'''
s+='''
#print axioms activeCodes_length
#print axioms activeCodeView_bounds
#print axioms literalSourceMatrix_active_entry
end
end AspisV8R19.R801LiteralActiveEntries
'''
pathlib.Path('.r21-scratch/R801LiteralActiveEntries.lean').write_text(s)
print('SHA',hashlib.sha256(s.encode()).hexdigest())
