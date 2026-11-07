from pathlib import Path
E=Path(__file__).resolve().parent
s=(E.parent/'rowspec-lead-20261107/RSL_TX2_241.lean').read_text()
t=s[s.index('def Ref '):];t=t[:t.index('\n\n')]
t=t.replace('def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) : RS Unit','def value (L : PoolLib) (D : DeployedIds) (V : V2Lib) (v : NND_PoolValues.Values L) (w : NND_Tx2Values.Values V) (a : Args) (env : Env) : Except ProgramError Unit')
t=t.replace('Spec.call TX2_242.Domain (TX2_242.Ref L D)\n            ⟨a.program_id, a.accounts, a.data, a.current_slot⟩','NND_ValidateEval.value L D v ⟨a.program_id, a.accounts, a.data, a.current_slot⟩ env')
t=t.replace('RS.lift (Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2)\n            (publicBytes, slice proofData AFTERSTATE_BYTES proofEnd, checkpointData))','Except.ok (w.auth publicBytes (slice proofData AFTERSTATE_BYTES proofEnd) checkpointData env)')
t=t.replace('RS.lift (L.encodeStatement validated.statement)','Except.ok (v.encode validated.statement env)')
for x,y in [('RS.bind','ebind'),('RS.seq','eseq'),('RS.check','echeck'),('RS.ofExcept','id'),('RS.ofOption','option'),('RS.index','indexValue'),('mapVErr V r','NND_Tx2Values.mapError r'),('L.emitResult validated.statement','v.emit validated.statement env')]:t=t.replace(x,y)
prefix='''import NND_ValidateEval
import NND_Tx2CallReturned
set_option autoImplicit false
namespace NND_Stage2Eval
open RSL RSL.TX2_241 NND_Returned
'''+t+'''

theorem returned (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (v : NND_PoolValues.Values L) (w : NND_Tx2Values.Values V) (a : Args) (env : Env) :
 Returns (Ref L D V a) env (value L D V v w a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (call _ _ _ env _ (NND_ValidateEval.returned L D v _ env))
 intro validated
 apply rs_bind _ _ env _ _ (index env _ _)
 intro acc0
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro proofData
 apply rs_bind _ _ env _ _ (index env _ _)
 intro acc6
 apply rs_bind _ _ env _ _ (ofExcept env _)
 intro checkpointData
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (rs_lift _ env _ (v.encode_ret _ env))
 intro enc
 apply rs_bind _ _ env _ _ (ofOption env _ _)
 intro publicBytes
 apply seq _ _ env _ _ (check env _ _)
 apply rs_bind _ _ env _ _ (NND_Tx2Values.call_returned V w _ _ _ env)
 intro r
 apply seq _ _ env _ _ (NND_Tx2Values.mapVErr_returned V r env)
 exact v.emit_ret _ env

#print axioms returned
end NND_Stage2Eval
'''
(E/'NND_Stage2Eval.lean').write_text(prefix)
