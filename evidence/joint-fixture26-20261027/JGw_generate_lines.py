from pathlib import Path
import re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
for i in range(10):
 v=(R/f'lean/JGw_Values{i}.lean').read_text();words=re.findall(r'def value : AspisR1RecordParser.field.wide_exact.WideExact := packed ([^\n]+)',v);assert len(words)==4
 ns=f'JGw_Line{i}'
 s=f'''import JGw_Values{i}
import JFn_LineArrayTotal
import JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values{i}.value.val[j.val]'(by rw [JGw_Values{i}.value.property];exact j.isLt)) := by
  fin_cases j
'''
 for j in range(4):
  ws=[int(x) for x in re.findall(r'(\d+)#u32',words[j])];assert len(ws)==8
  s+='  · change ('+' ∧ '.join(f'{w}<2147483647' for w in ws[:4])+') ∧ ('+' ∧ '.join(f'{w}<2147483647' for w in ws[4:])+')\n    omega\n'
 s+=f'''#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values{i}.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values{i}.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.{ns}
end
'''
 f=R/f'lean/{ns}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('checked' if '--check' in sys.argv else 'generated','ten native TX1 line returnability modules')
