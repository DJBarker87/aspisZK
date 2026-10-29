"""Emit named continuation stages and head-only successful-join composition.
Never simplify through an unconsumed continuation; do not raise any limit.
"""
from pathlib import Path
import sys,json,hashlib
L=Path('evidence/pv-b3p6-20261028/lean');old=(L/'PV_B3P_PublicDigestSuccess227.lean').read_text();prefix=old.split('theorem public_digest_success',1)[0]
prefix=prefix.replace('import PV_B3P_SemanticCallersSuccess227\nimport PV_B3P_CarrySuccess227','import PV_B3P_DigestFields227').replace('recipient_cps','recipient_continue8').replace('digest_level_cps','frontier_continue8')
prefix+='''/-- Eliminate only the head successful join, leaving the continuation opaque. -/
theorem digest_ok_continue8 {α β : Type} (x : α) (f : α → Result β)
    (h : Success (f x)) : Success (Result.ok x >>= f) := h
#print axioms digest_ok_continue8
end PV_B3P_Success227
'''
proof='theorem public_digest_success'+old.split('theorem public_digest_success',1)[1]
proof=proof.replace('public_digest_success','public_digest_success8').replace('recipient_cps','recipient_continue8').replace('digest_level_cps','frontier_continue8').replace('  simp only [bind_tc_ok]','  apply digest_ok_continue8')
header='''import PV_B3P_DigestContinue8227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry
'''
files={'PV_B3P_DigestContinue8227':prefix,'PV_B3P_DigestCps8227':header+proof}
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
print(json.dumps(dict(modules={m:hashlib.sha256(s.encode()).hexdigest()for m,s in files.items()},head_only_join_eliminations=proof.count('apply digest_ok_continue8'),whole_continuation_simplifications=proof.count('simp only [bind_tc_ok]'))))
