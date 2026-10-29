from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17/raw/terminal-digest';raw=(R/'Funs.lean').read_text();old=(D/'raw227-composition-resume5/Funs.lean').read_text()
def decls(s):
 out={}
 for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
  m=re.search(r'^def (\S+)',b,re.M)
  if m:out[m[1]]=re.split(r'^end PV_B3P_',b[m.start():],flags=re.M)[0].strip()
 return out
lex=lambda s:re.findall(r'\w+|[^\s]',s)
a,b=decls(raw),decls(old);targets=[];shared=[]
for n,t in a.items():
 if n.startswith('host_terminal.'):
  for c in ['DIGEST_ELEMS','MERKLE_NODE_COMPRESSION_V3_TWEAK']:t=t.replace('aspis_statement.poseidon2.'+c,'(Result.ok aspis_statement.poseidon2.'+c+')')
  targets.append(t)
 else:assert n in b and lex(t)==lex(b[n]),n;shared.append(n)
s='''import PV_B3P_DirectRange17227
import PV_B3P_NativeDigestStore15227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
'''+ '\n\n'.join(targets)+'''
end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Native15227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul aspis_core.field.QM31.sub aspis_core.field.M31.add Array.index_usize Array.update

theorem digest_body17 (selector : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) (start : Usize)
    (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool)
    (cursor : Usize) (output : Array aspis_core.field.QM31 8#usize) :
    host_terminal.add_digest_binding_loop.body 8#usize selector opened start expected tweak
      { start := cursor, «end» := 8#usize } output =
    if cursor < 8#usize then do
      let next ← digest_store_cell11 selector opened start expected tweak output cursor
      .ok (.cont ({ start := Usize.wrapping_add cursor 1#usize, «end» := 8#usize },next))
    else .ok (.done output) := by
  by_cases h : cursor < 8#usize <;>
    simp only [host_terminal.add_digest_binding_loop.body,range_next_extraction17,h,
      if_true,if_false,bind_tc_ok,digest_store_cell11,reference_terminal.tweak227,
      host_terminal.lift_m31,reference_terminal.lift_m31,
      aspis_statement.poseidon2.DIGEST_ELEMS,PV_B3P_Ordered227.bind_assoc]

theorem digest_loop_plan17 (selector : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) (start : Usize)
    (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool)
    (n : Nat) (cursor : Usize) (output : Array aspis_core.field.QM31 8#usize)
    (bound : cursor.val+n=8) :
    host_terminal.add_digest_binding_loop 8#usize { start := cursor, «end» := 8#usize }
      output selector opened start expected tweak =
    usize_plan (digest_store_cell11 selector opened start expected tweak) n cursor output := by
  induction n generalizing cursor output with
  | zero =>
    have stop : ¬ cursor < 8#usize := by scalar_tac
    unfold host_terminal.add_digest_binding_loop
    rw [loop.eq_1]
    simp only [digest_body17,stop,if_false,bind_tc_ok,usize_plan]
  | succ n ih =>
    have inside : cursor < 8#usize := by scalar_tac
    have inc := PV_B3P_Offset226V3.add_value cursor 1#usize
      (PV_B3P_Binding13227.range_increment_safe13 cursor 8#usize inside)
    have rest : (Usize.wrapping_add cursor 1#usize).val+n=8 := by omega
    unfold host_terminal.add_digest_binding_loop
    rw [loop.eq_1]
    simp only [digest_body17,inside,if_true,usize_plan,PV_B3P_Ordered227.bind_assoc]
    cases operation : digest_store_cell11 selector opened start expected tweak output cursor with
    | fail e => rfl
    | div => rfl
    | ok next =>
      simpa only [host_terminal.add_digest_binding_loop,bind_tc_ok,lift] using
        ih (Usize.wrapping_add cursor 1#usize) next rest

theorem digest_extraction_reference17 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool) :
    host_terminal.add_digest_binding output selector opened start expected tweak =
      reference_terminal.add_digest_binding output selector opened start expected tweak := by
  apply Eq.trans _ (native_digest_store_binding15 output selector opened start expected tweak)
  unfold host_terminal.add_digest_binding native_digest_store15
  simp only [aspis_statement.poseidon2.DIGEST_ELEMS,bind_tc_ok]
  rw [digest_loop_plan17 selector opened start expected tweak 8 0#usize output (by rfl),
    range_plan13 _ 0#usize 8#usize 8 output (by rfl)]
#print axioms digest_body17
#print axioms digest_loop_plan17
#print axioms digest_extraction_reference17
end PV_B3P_Direct17227
'''
(D/'lean/PV_B3P_DirectDigest17227.lean').write_text(s)
(D/'resume17/digest-port.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),shared_declarations_identical_tokens=shared,generated_definitions=len(targets),opaque_constant_instantiations=['DIGEST_ELEMS = Result.ok 8#usize','MERKLE_NODE_COMPRESSION_V3_TWEAK = Result.ok existing identical deployed constant'],raw_output_unedited=True,no_external_axiom_template_compiled=True),indent=2)+'\n')
