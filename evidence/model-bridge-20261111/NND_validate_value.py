from pathlib import Path
E=Path(__file__).resolve().parent
s=(E.parent/'rowspec-lead-20261107/RSL_TX2_242.lean').read_text()
t=s[s.index('def Ref '):];t=t[:t.index('\n\n')]
t=t.replace('def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS (Validated L)', 'def value (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L) (a : Args) (env : Env) : Except ProgramError (Validated L)')
t=t.replace('Spec.call TX2_233.Domain (TX2_233.Ref L D)\n            ⟨a.verifier_program, a.accounts, pool, lane, slot⟩','NND_AuthEval.value L D ⟨a.verifier_program, a.accounts, pool, lane, slot⟩ env')
for x,y in [('RS.bind','ebind'),('RS.seq','eseq'),('RS.check','echeck'),('RS.ofExcept','id'),('RS.ofOption','option'),('RS.pure','Except.ok'),('L.scanProof pdata','v.scan pdata env'),('L.reconstruct q auth scanned.1','v.reconstruct q auth scanned.1 env')]:t=t.replace(x,y)
prefix='''import NND_AuthEval
import NND_PoolValues
import RSL_TX2_242
set_option autoImplicit false
namespace NND_ValidateEval
open RSL RSL.TX2_242 NND_Returned
'''+t+'''

theorem returned (L : PoolLib) (D : DeployedIds) (v : NND_PoolValues.Values L) (a : Args) (env : Env) :
 Returns (Ref L D a) env (value L D v a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro q
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro lane
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro slot
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NND_AuthEval.returned L D _ env))
 intro auth
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro proofAccount
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro pdata
 apply rs_bind _ _ env _ _ (v.scan_ret pdata env)
 intro scanned
 apply rs_bind _ _ env _ _ (v.reconstruct_ret q auth scanned.1 env)
 intro statement
 exact rs_pure env _

#print axioms returned
end NND_ValidateEval
'''
(E/'NND_ValidateEval.lean').write_text(prefix)
