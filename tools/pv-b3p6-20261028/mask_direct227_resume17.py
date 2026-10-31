"""Parameterize the two unresolved externals; never install template axioms."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17';raw=(R/'host-recovery/direct-copy/selector_mask_sum_16/generated/Funs.lean').read_text()
def decls(s):
 out={}
 for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
  m=re.search(r'^def (\S+)',b,re.M)
  if m:out[m[1]]=re.split(r'^end PV_B3P_',b[m.start():],flags=re.M)[0].strip()
 return out
x=decls(raw);old=decls((D/'raw227-composition-resume5/Funs.lean').read_text());lex=lambda s:re.findall(r'\w+|[^\s]',s)
shared=[];parts=[]
for n,t in x.items():
 if not n.startswith('host_copy_terminal.selector_mask_sum_16'):
  assert n in old and lex(t)==lex(old[n]),n;shared.append(n);continue
 if n.endswith('.body'):
  t=t.replace(n+'\n',n+'\n  (trailing_zeros : U16 → Result U32)\n')
 elif n.endswith('_loop'):
  t=t.replace(n+'\n',n+'\n  (trailing_zeros : U16 → Result U32)\n').replace('host_copy_terminal.selector_mask_sum_16_loop.body\n','host_copy_terminal.selector_mask_sum_16_loop.body trailing_zeros\n')
 else:
  t=t.replace(n+'\n',n+'\n  (count_ones trailing_zeros : U16 → Result U32)\n').replace('host_copy_terminal.selector_mask_sum_16_loop values','host_copy_terminal.selector_mask_sum_16_loop trailing_zeros values')
 t=t.replace('core.num.U16.count_ones','count_ones').replace('core.num.U16.trailing_zeros','trailing_zeros');parts.append(t)
assert len(parts)==3
s='import PV_B3P_MaskWhile14227\nnamespace PV_B3P_227\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option autoImplicit false\n'+'\n\n'.join(parts)+'\nend PV_B3P_227\n'
s+='''namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add aspis_core.field.QM31.sub

def mask_add17 (values : Array aspis_core.field.QM31 16#usize)
    (sum : aspis_core.field.QM31) (index : U32) : Result aspis_core.field.QM31 := do
  let q ← Array.index_usize values (UScalar.cast .Usize index)
  aspis_core.field.QM31.add sum q

theorem mask_loop_stop17 (zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize) (sum : aspis_core.field.QM31) :
    host_copy_terminal.selector_mask_sum_16_loop zeros values 0#u16 false sum = .ok sum := by
  unfold host_copy_terminal.selector_mask_sum_16_loop
  rw [loop.eq_1]
  have zero : (0#u16 != 0#u16) = false := by rfl
  simp only [host_copy_terminal.selector_mask_sum_16_loop.body,zero,Bool.false_eq_true,if_false]

theorem mask_loop_step17 (zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (sum : aspis_core.field.QM31) (index : U32)
    (nonzero : mask ≠ 0#u16) (law : zeros mask = .ok index) :
    host_copy_terminal.selector_mask_sum_16_loop zeros values mask false sum = (do
      let next ← mask_add17 values sum index
      host_copy_terminal.selector_mask_sum_16_loop zeros values
        (mask &&& (U16.wrapping_sub mask 1#u16)) false next) := by
  unfold host_copy_terminal.selector_mask_sum_16_loop
  rw [loop.eq_1]
  have nonzero_bool : (mask != 0#u16) = true := by simp [nonzero]
  simp only [host_copy_terminal.selector_mask_sum_16_loop.body,nonzero_bool,if_true,
    law,lift,bind_tc_ok,Bool.false_eq_true,if_false,mask_add17,PV_B3P_Ordered227.bind_assoc]
  cases read : Array.index_usize values (UScalar.cast .Usize index) with
  | fail e => rfl
  | div => rfl
  | ok q =>
    simp only [bind_tc_ok]
    cases add : aspis_core.field.QM31.add sum q <;> rfl

theorem mask_entry17 (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (count : U32) (law : ones mask = .ok count) (small : ¬ count > 8#u32) :
    host_copy_terminal.selector_mask_sum_16 ones zeros values mask =
      host_copy_terminal.selector_mask_sum_16_loop zeros values mask false aspis_core.field.QM31.ZERO := by
  simp only [host_copy_terminal.selector_mask_sum_16,law,bind_tc_ok,small,if_false,
    Bool.false_eq_true]
  rfl

#print axioms mask_entry17
#print axioms mask_loop_stop17
#print axioms mask_loop_step17
end PV_B3P_Direct17227
'''
(D/'lean/PV_B3P_DirectMask17227.lean').write_text(s)
(R/'mask-port.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),shared_declarations_identical_tokens=shared,definition_count=3,external_parameters=['count_ones','trailing_zeros'],unresolved='exact intrinsic source laws; parameterization supplies no deployment credit',no_external_axiom_template_compiled=True,changes=['imports and namespace','explicit parameters for the two unresolved external dependencies, threaded unchanged']),indent=2)+'\n')
