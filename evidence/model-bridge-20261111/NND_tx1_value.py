from pathlib import Path
E=Path(__file__).resolve().parent
s=(E.parent/'rowspec-lead-20261107/RSL_TX1_345.lean').read_text()
s=s[s.index('def body'):s.index('\ndef Ref')]
s=s.replace('def body (V : VLib) (P : PreparedNew V)', 'def bodyValue (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P)')
s=s.replace(':\n    RS Bytes :=', '(env : Env) :\n    Except ProgramError Bytes :=')
a=s.index('Spec.call (TX1_328.Domain V)');b=s.index(') fun checkpoint =>',a)
s=s[:a]+'''NND_Tx1ReturnedValues.mapVErrValue V (F.tx1
            ⟨C.semanticPublic st, publicData, slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
             (a.data.getD 1 0).toNat⟩ env)'''+s[b:]
for a,b in [('RS.seq','eseq'),('RS.bind','ebind'),('RS.ofExcept','id'),('RS.ofOption','option'),('RS.lift Spec.alloc','Except.ok ()'),('RS.check','echeck'),('RS.pure','Except.ok')]:s=s.replace(a,b)
header='''import NND_Tx1ReturnedValues
set_option autoImplicit false
namespace NND_Stage1Eval
open RSL RSL.TX1_345 NND_Returned
'''
proof='''
syntax "stage1_steps " term : tactic
macro_rules
| `(tactic| stage1_steps $env:term) => `(tactic|
 first
 | exact NND_Tx1ReturnedValues.first_returned _ _ _ _ $env
 | exact NND_Returned.ofExcept $env _
 | exact NND_Returned.ofOption $env _ _
 | exact NND_Returned.check $env _ _
 | exact NND_Returned.rs_lift _ $env () (NND_Returned.alloc $env)
 | exact NND_Returned.rs_pure $env _
 | (apply NND_Returned.seq <;> stage1_steps $env)
 | (apply NND_Returned.rs_bind <;> stage1_steps $env)
 | (intro; stage1_steps $env))

theorem body_returned (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P)
 (C : S1Lib V) (a : Args) (p pub ck : OwnedAccount) (env : Env) :
 Returns (body V P C a p pub ck) env (bodyValue V P F C a p pub ck env) := by
 unfold body bodyValue
 stage1_steps env

#print axioms body_returned
end NND_Stage1Eval
'''
(E/'NND_Stage1Eval.lean').write_text(header+s+proof)
