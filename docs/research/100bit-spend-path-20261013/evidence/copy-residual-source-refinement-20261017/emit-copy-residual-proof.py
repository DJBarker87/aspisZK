from pathlib import Path
import hashlib
header='''import CopyResidualSource

/-! Source refinement of the actual Copy rational residual, reusing the
checked QM31 arithmetic lemmas. No source arithmetic success is an input. -/
set_option autoImplicit false
namespace AspisR1.CopyResidualExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Row := AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.CopyRowExtension
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def cell (xs : Array QM 2#usize) (i : Fin 2) : QM :=
  xs.val[i.val]'(by simpa [xs.property] using i.isLt)

def modelRow (row : Row) : R0P.CopyRowExtension ExactQM :=
  ⟨fun i => decode (cell row.producer_values i),
   fun i => decode (cell row.producer_weights i),
   fun i => decode (cell row.consumer_values i),
   fun i => decode (cell row.consumer_weights i)⟩
'''
lines=[header]
for i in range(2):
 lines.append(f'''private theorem read_two_{i} (xs : Array QM 2#usize) :
    Array.index_usize xs {i}#usize = .ok (cell xs {i}) := by
  simpa [cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    xs {i}#usize (by norm_num)
''')
for i,n in enumerate(['a','b','c','d']):
 lines.append(f'''private theorem read_four_{i} (a b c d : QM) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) {i}#usize = .ok {n} := by
  simpa [Array.make] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array.make 4#usize [a,b,c,d]) {i}#usize (by norm_num)
''')
lines.append('''/-- Canonical row cells, helper and challenge suffice for actual source
success and the exact retained Copy residual polynomial. Pattern/link and
active-mask production remain enclosing-caller obligations. -/
theorem copy_residual_exact (row : Row) (helper chi : QM)
    (hpv : ∀ i : Fin 2, CanonicalQM (cell row.producer_values i))
    (hpw : ∀ i : Fin 2, CanonicalQM (cell row.producer_weights i))
    (hcv : ∀ i : Fin 2, CanonicalQM (cell row.consumer_values i))
    (hcw : ∀ i : Fin 2, CanonicalQM (cell row.consumer_weights i))
    (hhelper : CanonicalQM helper) (hchi : CanonicalQM chi) :
    ∃ out,
      AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual
        row helper chi = .ok out ∧ CanonicalQM out ∧
      decode out = R0P.copyResidual (modelRow row) (decode helper) (decode chi) := by
''')
inputs={'p0':('producer_values',0,'hpv'),'p1':('producer_values',1,'hpv'),'c0':('consumer_values',0,'hcv'),'c1':('consumer_values',1,'hcv'),'pw0':('producer_weights',0,'hpw'),'pw1':('producer_weights',1,'hpw'),'cw0':('consumer_weights',0,'hcw'),'cw1':('consumer_weights',1,'hcw')}
for n,(field,i,h) in inputs.items():lines.append(f'  let {n} := cell row.{field} {i}\n  have hc{n} : CanonicalQM {n} := {h} {i}\n')
ops=[('q1','sub','chi','p0'),('q3','sub','chi','p1'),('q5','sub','chi','c0'),('q7','sub','chi','c1'),('producer_denominator','mul','q1','q3'),('consumer_denominator','mul','q5','q7'),('q13','mul','pw0','q3'),('q15','mul','pw1','q1'),('producer_numerator','add','q13','q15'),('q17','mul','cw0','q7'),('q19','mul','cw1','q5'),('consumer_numerator','add','q17','q19'),('q20','mul','helper','consumer_denominator'),('q21','add','q20','consumer_numerator'),('q22','mul','producer_denominator','q21'),('q23','mul','consumer_denominator','producer_numerator'),('out','sub','q22','q23')]
for n,op,a,b in ops:
 owner='AspisR1.EqualityValueAdapter' if op=='sub' else 'AspisR1.ExtractedMaskQM31Exact'
 canon=lambda x:{'chi':'hchi','helper':'hhelper'}.get(x,'hc'+x)
 lines.append(f'  obtain ⟨{n}, h{n}, hc{n}, hv{n}⟩ :=\n    {owner}.current_qm_{op}_exact {a} {b} {canon(a)} {canon(b)}\n')
 symbol={'sub':'-','add':'+','mul':'*'}[op]
 lines.append(f'  change decode {n} = decode {a} {symbol} decode {b} at hv{n}\n')
lines.append('  refine ⟨out, ?_, hcout, ?_⟩\n  · simp only [AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual,\n')
simpl=['read_two_0','read_two_1']+['read_four_'+str(i) for i in range(4)]+list(inputs)+['h'+n for n,*_ in ops]+['bind_tc_ok']
lines.append('      '+', '.join(simpl)+']\n')
lines.append('''  · change decode out =
      (decode chi - decode p0) * (decode chi - decode p1) *
        (decode helper * ((decode chi - decode c0) * (decode chi - decode c1)) +
          (decode cw0 * (decode chi - decode c1) + decode cw1 * (decode chi - decode c0))) -
      ((decode chi - decode c0) * (decode chi - decode c1)) *
        (decode pw0 * (decode chi - decode p1) + decode pw1 * (decode chi - decode p0))
''')
lines.append('    rw ['+', '.join('hv'+n for n,*_ in reversed(ops))+']\n\n#print axioms copy_residual_exact\nend\nend AspisR1.CopyResidualExact\n')
p=Path('/tmp/CopyResidualExact-c.lean');p.write_text(''.join(lines));print(hashlib.sha256(p.read_bytes()).hexdigest())
