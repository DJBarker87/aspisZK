from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[3]
src=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=src.read_text(); start=s.index('    let a := Array.repeat 64#usize 0#u8',s.index('def\n  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body'))
cut=s.index('    let (r, s1) ← getrandom.fill s',start)
end=s.index('\n  else\n    ok (done',cut)
prefix=s[start:cut];suffix=s[cut+len('    let (r, s1) ← getrandom.fill s\n'):end]
def dedent(t):return '\n'.join(x[4:] if x.startswith('    ') else x for x in t.splitlines())
text='''import R1Z.ProverRwEntropyIteration

/-! Exact call-site factoring of the retained emitted entropy body.
This proves a pure specialization equation, not a native effect transport. -/
set_option autoImplicit false
namespace R1Z.ProverRwEffectSource
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Secret := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Status := core.result.Result Secret aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
abbrev Reply := (core.result.Result Unit getrandom.error.Error) × Slice U8
abbrev Back := Slice U8 → zeroize.Zeroizing (Array U8 64#usize)
abbrev Outcome := ControlFlow Usize Status

def before : Result (Slice U8 × Back) := do
'''+ '\n'.join('  '+x for x in dedent(prefix).splitlines())+'''
  ok (s, as_mut_back)

def after (mask_nonce : Array U8 32#usize) (retry : Usize)
    (as_mut_back : Back) (reply : Reply) : Result Outcome := do
  let (r,s1) := reply
'''+ '\n'.join('  '+x for x in dedent(suffix).splitlines())+'''

def staged (nonce : Array U8 32#usize) (limit retry : Usize) : Result Outcome := do
  if retry < limit then
    let (input,back) ← before
    let reply ← getrandom.fill input
    after nonce retry back reply
  else ok (done (.Err .RepeatedZeroBlock))

theorem staged_eq (nonce : Array U8 32#usize) (limit retry : Usize) :
    staged nonce limit retry =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        nonce limit retry := by
  unfold staged before after
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  split <;> simp only [bind_assoc, Aeneas.Std.uncurry, bind_tc_ok]
  repeat' first
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
      try (change (_ × _) at value; rcases value with ⟨value1,value2⟩)
      simp only [Aeneas.Std.uncurry, bind_tc_ok]
    | rfl

#print axioms staged_eq
end R1Z.ProverRwEffectSource
'''
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEffectSource.lean';out.write_text(text)
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/effect';e.mkdir(exist_ok=True)
(e/'factoring.json').write_text(json.dumps(dict(source=str(src.relative_to(root)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),output=str(out.relative_to(root)),output_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),checked_claim='staged_eq: exact pure body equality; arbitrary-world interpretation is not native source correspondence'),indent=2)+'\n')
