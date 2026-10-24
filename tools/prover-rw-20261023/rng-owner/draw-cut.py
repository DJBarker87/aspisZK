from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'ProverRwRngEmission.lean').read_text()
a=s.index('    let bytes1 := deref_mut_back a2',s.index('def StateOnlyAttemptSecrets.generate_with_loop.body'))
b=s.index('\n  else\n    ok (done (provider,',a)
tail=s[a:b].replace('    let bytes1 := deref_mut_back a2','  let bytes1 := a2',1)
# Preserve every emitted tail operation; only remove the now-transparent borrow
# continuation already installed in the unchanged common emission.
out='''import R1Z.ProverRwRngOwnerEvents
import R1Z.ProverRwRngTape
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerDraw
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerEvents
variable [ErasureFns]
def afterFill (mask_nonce : Array U8 32#usize) (retry : Usize)
    (reply : (Tape × core.result.Result Unit U8) × Array U8 64#usize) :
    Result (ControlFlow State (Tape × Status)) := do
  let ((after,result),a2) := reply
'''+tail+'''

theorem draw_factor (nonce : Array U8 32#usize) (p : Tape) (retry : Usize) :
    newBody nonce (p,retry) =
      if retry < 16#usize then
        (Tape.Insts.Prover_rw_rng_preflightDraw64.fill p (Array.repeat 64#usize 0#u8) >>=
          afterFill nonce retry)
      else .ok (.done (p,.Err .RepeatedZeroBlock)) := by
  unfold newBody StateOnlyAttemptSecrets.generate_with_loop.body
  split
  · simp only [zeroize.Zeroizing.new,
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry]
    rfl
  · rfl
#print axioms draw_factor
end R1Z.ProverRwRngOwnerDraw
'''
(L/'ProverRwRngOwnerDraw.lean').write_text(out)
(D/'draw-cut.json').write_text(json.dumps({'source_module_sha256':hashlib.sha256(s.encode()).hexdigest(),'complete_tail_span':[a,b],'complete_tail_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'output_sha256':hashlib.sha256(out.encode()).hexdigest(),'normalization':'transparent identity deref_mut_back removed; all emitted tail operations retained; draw_factor checked by kernel','scope':'observe exact input and advanced provider; not physical erasure'},indent=2)+'\n')
