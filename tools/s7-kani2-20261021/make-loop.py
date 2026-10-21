from pathlib import Path
import hashlib,json,sys,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean'
s=p.read_text();a=s.index('def accumulate_rows_owned\n');b=s.index('partial_fixpoint',a)+len('partial_fixpoint');original=s[a:b]
body=original
edits={'aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31':'backend.from_m31','aspis_core.field.wide_exact.WideExact.from_qm31':'backend.from_qm31','trace.value':'backend.trace','push_owned':'backend.push','aspis_core.field.QM31':'K','aspis_core.field.M31':'U32','def accumulate_rows_owned\n':'def accumulate_rows_owned (backend : Backend)\n','accumulate_rows_owned output_weights':'accumulate_rows_owned backend output_weights'}
for old,new in edits.items():body=body.replace(old,new)
header='''import Aeneas
import ExtractedCurrentReducerOps
import Lean.Elab.Tactic.Omega

/- Literal emitted row driver with explicit backend parameters. Backend laws
are not axioms and no concrete backend or production-caller join is assumed. -/
set_option autoImplicit false
namespace S7Kani2AccumulatorLoop
open Aeneas Aeneas.Std Result
structure K where
  c0 : U32 × U32
  c1 : U32 × U32
structure E where
  c0 : K
  c1 : K
structure BatchedWeights where
  raw : alloc.vec.Vec (Array U64 4#usize)
  terms : Usize
structure Backend where
  push : BatchedWeights → Usize → K → U32 → Result BatchedWeights
  from_qm31 : K → Result E
  from_m31 : U32 → Result E
  trace : U16 → Usize → E → Result Unit
abbrev State := alloc.vec.Vec K × BatchedWeights

'''
step=body[body.index('    let m ←'):body.index('    let i3 ←')]
step=re.sub(r'\boutput_weights\b','state.1',step)
step=re.sub(r'\bweights\b','state.2',step)
header+='''def step (backend : Backend) (basis : Array U32 256#usize)
    (power : K) (next width j : Usize) (state : State) : Result State := do
'''+ '\n'.join(l[2:] for l in step.rstrip().splitlines())+'''
  ok (state.1, weights1)

'''
tail='''
def iterate (f : Usize → State → Result State) : Nat → Usize → State → Result State
 | 0, _, state => ok state
 | n+1, j, state => do
     let state1 ← f j state
     let j1 ← j + 1#usize
     iterate f n j1 state1

/-- The checked increment is total on every nonterminal production row. -/
theorem increment (j : Usize) (h : j.val < 256) :
    ∃ j1, (j + 1#usize : Result Usize) = ok j1 ∧ j1.val = j.val+1 := by
  apply AspisR1.ExtractedCurrentReducerOps.tryMk_success
  have hb : 256 < 2^UScalarTy.Usize.numBits := by scalar_tac
  change j.val + 1 < 2^UScalarTy.Usize.numBits
  omega

/-- Actual emitted recurrence equals bounded composition, retaining checked
errors and divergence from each backend step. No step-success premise. -/
theorem extracted_loop_composition (backend : Backend)
    (basis : Array U32 256#usize) (power : K) (next width j : Usize)
    (n : Nat) (state : State) (hwidth : width.val ≤ 256)
    (remaining : j.val+n=width.val) :
    accumulate_rows_owned backend state.1 state.2 basis power next width j =
      iterate (step backend basis power next width) n j state := by
  induction n generalizing j state with
  | zero =>
      have stop : j ≥ width := by scalar_tac
      rw [accumulate_rows_owned]
      simp only [stop, if_pos, iterate]
  | succ n ih =>
      rcases state with ⟨output_weights, weights⟩
      have running : ¬ j ≥ width := by scalar_tac
      obtain ⟨j1, hj1, hv⟩ := increment j (by omega)
      rw [accumulate_rows_owned]
      simp only [running, if_false, iterate, step, bind_tc_ok, bind_assoc_eq]
      congr 1
      funext m
      congr 1
      funext weights1
      congr 1
      funext i
      congr 1
      funext i1
      congr 1
      funext q
      congr 1
      funext we
      congr 1
      funext unit1
      congr 1
      funext i2
      congr 1
      funext we1
      congr 1
      funext unit2
      simp only [hj1, bind_tc_ok]
      exact ih j1 (output_weights,weights1) (by omega)

#print axioms increment
#print axioms extracted_loop_composition
end S7Kani2AccumulatorLoop
'''
text=header+body+'\n'+tail
out=B/'lean/S7Kani2AccumulatorLoop.lean'
manifest=dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(original.encode()).hexdigest(),replacements=edits,scope='Exact recurrence declaration modulo explicit backend parameters and structural field carriers; no external axiom placeholders imported.')
if '--check' in sys.argv:assert out.read_text()==text
else:out.write_text(text)
(B/'evidence/s7-kani2-20261021/loop-binding.json').write_text(json.dumps(manifest,indent=2)+'\n')
