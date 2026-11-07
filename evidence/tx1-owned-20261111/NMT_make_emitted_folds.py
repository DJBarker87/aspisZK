"""Expose original full-result cut continuation, not a successful-child law.
Fresh-body syntax stays byte-pinned; named folds are intermediate until all
child interpretations and caller clauses are installed.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
# Extract each fresh function signature, retaining all explicit parameter types.
def split_root(fn,root):
 s=(E/f'NMT_{fn}.Funs.lean').read_text();start=s.index('def '+root)
 sigbody=s[start:];split=sigbody.index(':= do');sig=sigbody[:split];body=sigbody[split+len(':= do'):];body=body[:body.index('\nend NMT_')]
 return sig,body
# 328 is a single full Result bind; the std mapper is instantiated, not assumed.
sig,body=split_root('first','first_decoded')
# Reuse the explicit signature and change only the function name for the reference.
text='''import NMT_first.Funs
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_first
open Aeneas Aeneas.Std Result
/-- Std Result::map_err, with the actual callback invoked only on Err. -/
def NMT_std_map_err {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
 (r : core.result.Result T E) (o : O) : Result (core.result.Result T F) :=
 match r with
 | .Ok value => .ok (.Ok value)
 | .Err error => do let mapped ← inst.call_once o error; .ok (.Err mapped)
'''
# Generic relational fold lemma is useful to both adapters; no row credit.
text+='''/-- All native outer Result arms are retained. A stopped child never invokes
its continuation, so a stopped prefix acquires no suffix callback. -/
theorem NMT_bind_complete {A B : Type} (r : Result A) (k : A → Result B) :
 (r >>= k) = match r with
 | .ok a => k a
 | .fail e => .fail e
 | .div => .div := by
 cases r <;> rfl
#print axioms NMT_bind_complete
'''
# Extract exact binders by finding final public1 argument.
start=sig.index('(NMT_call_0');end=sig.index('\n  (public1')
params=sig[start:end];params=params[params.index(' (NMT_call_1')+1:] # remove std mapper parameter
inputpart=sig[end:]
# New exact reference equation with all params visible, std mapper fixed.
text+='''/-- Fresh emitted328, std mapper interpreted by its complete library law.
This is an emitted-body fold, not a native row root or a child endpoint premise. -/
'''
text+='theorem NMT_emitted_fold '+params+inputpart.replace(':\n  Result (core.result.Result (alloc.vec.Vec Std.U8)\n    solana_program_error.ProgramError)\n  ',':\n  first_decoded NMT_std_map_err NMT_call_1 NMT_call_4 NMT_call_5 NMT_call_6 public1 public_bytes proof k =\n  (do\n    let r ← NMT_call_1 (SolanaDigest.Insts.Aspis_coreDigestDigest32 NMT_call_4 NMT_call_5) public1 public_bytes proof k () none\n    match r with\n    | .Ok bytes => .ok (.Ok bytes)\n    | .Err e => do let mapped ← NMT_call_6 e; .ok (.Err mapped))\n  ')
text+=':= by\n unfold first_decoded observer NMT_std_map_err\n simp only [bind_tc_ok, BuiltinFnOnce, AspisR1.NMT_CallTree.result_right, AspisR1.NMT_CallTree.result_assoc]\n cases h : NMT_call_1 (SolanaDigest.Insts.Aspis_coreDigestDigest32 NMT_call_4 NMT_call_5) public1 public_bytes proof k () none with\n | fail e => simp only [h,bind_tc_fail]\n | div => simp only [h,bind_tc_div]\n | ok r => cases r <;> simp only [h,bind_tc_ok]\n#print axioms NMT_emitted_fold\nend NMT_first\n'
(E/'NMT_328Fold.lean').write_text(text)
