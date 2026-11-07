from pathlib import Path
E=Path(__file__).resolve().parent
s=(E.parent/'rowspec-lead-20261107/RSL_TX2_234.lean').read_text()
prefix='''import NND_PoolReturned
import RSL_TX2_234
set_option autoImplicit false
namespace NND_RegistryEval
open RSL RSL.TX2_234 NND_Returned

def pdaValue (env : Env) (seeds : List Bytes) (program : B32) : Except ProgramError B32 :=
 option (env.pda seeds program) .invalidAccountData
'''
for a,b in [('immutableBranch','immutableValue'),('v1Branch','v1Value'),('Ref','value')]:
 t=s[s.index('def '+a+' '):];t=t[:t.index('\n\n')]
 t=t.replace('def '+a+' ','def '+b+' ').replace('(a : Args) : RS Unit','(a : Args) (env : Env) : Except ProgramError Unit')
 for x,y in [('RS.bind','ebind'),('RS.seq','eseq'),('RS.check','echeck'),('RS.ofExcept','id'),('RS.ofOption','option'),('RS.pure','Except.ok'),('pdaOrErr','pdaValue env'),('immutableBranch L D a','immutableValue L D a env'),('v1Branch L D a','v1Value L D a env')]:t=t.replace(x,y)
 prefix+='\n'+t+'\n'
prefix+='''
syntax \"registry_steps \" term : tactic
macro_rules
| `(tactic| registry_steps $env:term) => `(tactic|
 first
 | exact NND_Returned.ofExcept $env _
 | exact NND_Returned.ofOption $env _ _
 | exact NND_Returned.pdaOrErr $env _ _
 | exact NND_Returned.check $env _ _
 | exact NND_Returned.rs_pure $env _
 | (apply NND_Returned.seq <;> registry_steps $env)
 | (apply NND_Returned.rs_bind <;> registry_steps $env)
 | (intro; registry_steps $env))

theorem immutable_returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (immutableBranch L D a) env (immutableValue L D a env) := by
 unfold immutableBranch immutableValue
 registry_steps env

theorem v1_returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (v1Branch L D a) env (v1Value L D a env) := by
 unfold v1Branch v1Value
 registry_steps env

theorem returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (Ref L D a) env (value L D a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (ofExcept env _)
 split
 · exact immutable_returned L D a env
 · exact v1_returned L D a env

#print axioms immutable_returned
#print axioms v1_returned
#print axioms returned
end NND_RegistryEval
'''
(E/'NND_RegistryEval.lean').write_text(prefix)
