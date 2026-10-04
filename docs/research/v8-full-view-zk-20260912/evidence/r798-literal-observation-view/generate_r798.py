import pathlib,csv,json,hashlib
b=pathlib.Path('docs/research/v8-full-view-zk-20260912'); raw=b/'evidence/r769-point1-selected-entries/inputs/matrix.raw.tsv';assert hashlib.sha256(raw.read_bytes()).hexdigest()=='91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af'
tab=list(csv.reader(raw.open(),delimiter='\t'));codes=[int(r[2].removeprefix('active_chord_')) for r in tab[243:457]];assert len(codes)==214 and codes[-1]==1022
cols=json.loads((b/'evidence/r769-point1-selected-entries/lead-mapping-check.json').read_text())['exact_selected_columns'];headers={int(r[1]):(int(r[2]),int(r[3])-1) for r in tab[1:243]};pairs=[headers[x] for x in cols]
names=[];facts=[]
for i in range(222):
 if i<8:
  ns='AspisV8R19.R790LiteralObservationOrderPrototype'; names.append(f'{ns}.obs{i}');facts.append(f'{ns}.row{i}_selectedColumn')
 else:
  gi=(i-8)//16;ns=f'AspisV8R19.R790LiteralObservationChunk{gi:02d}'
  if i<213: stem=f'{i:03d}';names.append(f'{ns}.obs_{stem}');facts.append(f'{ns}.row_{stem}_selectedColumns')
  elif i==213:names.append(f'{ns}.obs_top');facts.append(f'{ns}.top_selectedColumns')
  elif i<217: stem=f'point_{i-214}';names.append(f'{ns}.obs_{stem}');facts.append(f'{ns}.{stem}_selectedColumns')
  else:stem=f'coeff_{i-217}';names.append(f'{ns}.obs_{stem}');facts.append(f'{ns}.{stem}_selectedColumns')
keys=[f'(0,{x})' for x in codes]+[f'(1,{i})' for i in range(3)]+[f'(2,{i})' for i in range(5)]
source='''import AspisV8R19.R797ObservationEncoding
import AspisV8R19.R790LiteralObservationChunk13
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R798LiteralObservationView
open AspisV8R19.R797ObservationEncoding
open AspisV8R19.R746SelectedJointMinor
noncomputable section

-- Literal list access and 222 small integer pairs only; no field recurrence is reduced.
def sourceObservations : List Obs := [\n'''+',\n'.join(names)+''']
def literalKeys : List (Nat × Nat) := ['''+', '.join(keys)+''']
theorem sourceObservations_length : sourceObservations.length = 222 := rfl
theorem sourceObservations_keys : sourceObservations.map observationKey = literalKeys := rfl
theorem literalKeys_nodup : literalKeys.Nodup := by decide

theorem sourceObservations_nodup : sourceObservations.Nodup := by
  apply List.Nodup.of_map observationKey
  rw [sourceObservations_keys]
  exact literalKeys_nodup

def sourceView (i : Fin 222) : Obs :=
  sourceObservations.get (Fin.cast sourceObservations_length.symm i)

theorem sourceView_injective : Function.Injective sourceView := by
  intro i j h
  have he := sourceObservations_nodup.injective_get h
  exact Fin.ext (congrArg Fin.val he)

theorem sourceView_bijective : Function.Bijective sourceView := by
  constructor
  · exact sourceView_injective
  · by_contra h
    have ht := Fintype.card_lt_of_injective_not_surjective sourceView sourceView_injective h
    rw [Fintype.card_fin, observation_card] at ht
    omega

noncomputable def sourceObservationEquiv : Fin 222 ≃ Obs :=
  Equiv.ofBijective sourceView sourceView_bijective

def literalColumns : List (Fin 255 × Fin 3) := ['''+', '.join(f'(⟨{d}, by decide⟩,⟨{s}, by decide⟩)' for d,s in pairs)+''']
theorem literalColumns_length : literalColumns.length = 222 := rfl

def columnView (i : Fin 222) : Fin 255 × Fin 3 :=
  literalColumns.get (Fin.cast literalColumns_length.symm i)

theorem selectedColumns_sourceView (i : Fin 222) :
    selectedColumns (sourceView i) = columnView i := by
  fin_cases i
'''
source+='\n'.join(f'  case «{i}» => exact {f}' for i,f in enumerate(facts))
source+='\n\n'+ '\n'.join('#print axioms '+x for x in ['sourceObservations_length','sourceObservations_keys','literalKeys_nodup','sourceObservations_nodup','sourceView_injective','sourceView_bijective','sourceObservationEquiv','literalColumns_length','selectedColumns_sourceView'])+'\nend\nend AspisV8R19.R798LiteralObservationView\n'
pathlib.Path('.r21-scratch/R798LiteralObservationView.lean').write_text(source)
print('generated exact 222 source observations and headers; SHA',hashlib.sha256(source.encode()).hexdigest())
