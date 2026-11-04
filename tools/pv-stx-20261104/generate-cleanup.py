"""Add the Rust lexical drop/Err restoration edges to the checked entropy lift.
This records a source-control reconstruction, not a native destructor proof.
"""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-stx-20261104')
s=Path('lean/PV_STX_Entropy.lean').read_text()
b=s[s.index('def\n  entropyBody'):s.index('theorem erases_bind')]
b=b.replace('Request.', 'Request.entropy <| PV_STX_Entropy.Request.')
zi=''
# Source lexical-scope order: retry increment, leaf, field, bytes.
cleanup='''          let _ ← Code.call (Request.drop 32 leaf_salt_seed1)
          let _ ← Code.call (Request.drop 32 field_mask_entropy1)
          let _ ← Code.call (Request.drop 64 bytes1)
'''
b=b.replace('          pure (cont retry1)',cleanup+'          pure (cont retry1)')
b=b.replace('        pure (cont retry1)', '''        let _ ← Code.call (Request.drop 32 leaf_salt_seed1)
        let _ ← Code.call (Request.drop 32 field_mask_entropy1)
        let _ ← Code.call (Request.drop 64 bytes1)
        pure (cont retry1)''',1) if False else b
# Handle the outer false branch separately, without touching the nested branch.
old='''        pure (cont retry1)
    | core.ops.control_flow.ControlFlow.Break'''
new='''        let _ ← Code.call (Request.drop 32 leaf_salt_seed1)
        let _ ← Code.call (Request.drop 32 field_mask_entropy1)
        let _ ← Code.call (Request.drop 64 bytes1)
        pure (cont retry1)
    | core.ops.control_flow.ControlFlow.Break'''
assert old in b;b=b.replace(old,new)
old='''          pure (done (core.result.Result.Ok'''
assert old in b;b=b.replace(old,'''          let _ ← Code.call (Request.drop 64 bytes1)
          pure (done (core.result.Result.Ok''')
old='''      pure (done r1)'''
assert old in b;b=b.replace(old,'''      let bytes1 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 9 as_mut_back s1)
      let _ ← Code.call (Request.drop 64 bytes1)
      pure (done r1)''')
prefix='''import PV_STX_Account
set_option autoImplicit false
noncomputable section
namespace PV_STX_EntropyCleanup
open Aeneas Aeneas.Std ProverRwFull ControlFlow PV_STX_Code PV_STX_DenoteRules
variable [ExternalTypes]
inductive Request : Type → Type 1 where
  | entropy {X : Type} (op : PV_STX_Entropy.Request X) : Request X
  | drop {Z : Type} (size : Nat) (value : zeroize.Zeroizing Z) : Request Unit
variable [ExternalFuns]
/-- Value erasure ONLY. Native drops are requests and cannot be inferred silent. -/
def fixed : {X : Type} → Request X → Result X
  | _,.entropy op => PV_STX_Entropy.fixed op
  | _,.drop _ _ => .ok ()
def nonzero (bytes : Array U8 32#usize) : Code Request Bool :=
  PV_STX_Map.map (fun op => Request.entropy op) (PV_STX_Entropy.nonzero bytes)
theorem nonzero_erases (bytes : Array U8 32#usize) :
    denote fixed (nonzero bytes) = aspis_prover.state_only_entropy.entropy_nonzero32 bytes := by
  rw [nonzero,PV_STX_Map.denote_map (fun op => Request.entropy op) PV_STX_Entropy.fixed fixed (fun _ => rfl)]
  exact PV_STX_Entropy.nonzero_erases bytes

'''
proof='''
theorem body_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyBody nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit retry := by
  unfold entropyBody aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  by_cases h : retry < limit
  · simp only [h,if_true]
    apply PV_STX_Entropy.erases_bind (fixed := fixed)
    · rfl
    · intro bytes
      apply PV_STX_Entropy.erases_bind (fixed := fixed)
      · rfl
      · rintro ⟨s,back⟩
        apply PV_STX_Entropy.erases_bind (fixed := fixed)
        · rfl
        · rintro ⟨r,s1⟩
          apply PV_STX_Entropy.erases_bind (fixed := fixed)
          · rfl
          · intro cf
            cases cf <;> simp only [bind_rule,call_rule,result_rule,pure_rule,if_rule,
              fixed,PV_STX_Entropy.fixed,nonzero_erases,Aeneas.Std.bind_tc_ok]
            all_goals simp only [Bind.bind,Aeneas.Std.bind]
            all_goals repeat first | rfl | split
  · simp only [h,if_false,pure_rule]

#print axioms nonzero_erases
#print axioms body_erases
end PV_STX_EntropyCleanup
'''
# erases_bind is specialized to the OLD Request family; supply our own local law.
law='''theorem erases_bind {A B : Type} (code : Code Request A) (next : A → Code Request B)
    (r : Result A) (f : A → Result B)
    (hc : denote fixed code = r) (hk : ∀ a, denote fixed (next a) = f a) :
    denote fixed (code >>= next) = (do let a ← r; f a) := by
  rw [bind_rule,hc]
  congr 1
  funext a
  exact hk a

'''
proof=proof.replace('PV_STX_Entropy.erases_bind (fixed := fixed)','erases_bind')
out=prefix+law+b+proof.replace('#print axioms nonzero_erases','#print axioms erases_bind\n#print axioms nonzero_erases')
paths={'lean/PV_STX_EntropyCleanup.lean':out}
manifest=dict(entropy_lift_sha256=hashlib.sha256(s.encode()).hexdigest(),rust_sha256=hashlib.sha256((E/'frozen-source/state_only_entropy.rs.txt').read_bytes()).hexdigest(),rust_lines=[216,243],changes=['restore partial error buffer after residual conversion','drop 64-byte owner on OS Err','drop 64-byte temporary before successful return','drop leaf then field then temporary after retry increment on both rejection branches'],native_destructor_association='OPEN; no native/world cleanup handler certified')
paths[str(E/'entropy-cleanup-generation.json')]=json.dumps(manifest,indent=2)+'\n'
for name,content in paths.items():
 p=Path(name)
 if '--check' in sys.argv: assert p.read_text()==content,name
 else:p.write_text(content)
print('cleanup generator check' if '--check' in sys.argv else 'generated cleanup lift')
