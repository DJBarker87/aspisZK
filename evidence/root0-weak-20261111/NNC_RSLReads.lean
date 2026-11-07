import NNC_RSLAuth
set_option autoImplicit false
namespace NNC_RSLReads
open RSL RSL.TX2_241 NMS_RSLRefine NMS_RSLStepFacts
/-- Accepted-reference cuts only. No endpoint is an input of this packet. -/
structure Cut (V : V2Lib) (a : Args) (env : Env) where
 acc0 : OwnedAccount
 acc6 : OwnedAccount
 proofData : Bytes
 checkpointData : Bytes
 publicBytes : Bytes
 n : Nat
 verifyEvents : List Event
 count : a.accounts.length=7
 index0 : a.accounts[0]?=some acc0
 index6 : a.accounts[6]?=some acc6
 read0 : acc0.bytes=.ok proofData
 read6 : acc6.bytes=.ok checkpointData
 proofLength : proofData.length=AFTERSTATE_BYTES+n
 publicLength : publicBytes.length=STATEMENT_BYTES
 domain : Dom064 V (publicBytes,slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+n),checkpointData)
 verified : V.tx2auth publicBytes (slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+n)) checkpointData
  env ⟨.ret (.ok ()),verifyEvents⟩
/-- Split replacement for the retired whole-unroll final-assembly shape:
source prefix inversion composes the separately checked verifier suffix. -/
theorem from_reference (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args)
 (env : Env) (events : List Event)
 (run : Ref L D V a env ⟨.ret (.ok ()),events⟩) : Nonempty (Cut V a env) := by
 unfold Ref at run
 obtain ⟨u,_,_,guard,h,_⟩ := rsbind_return _ _ _ _ _ run
 have passed := check_return _ _ _ _ guard
 simp only [Bool.or_eq_false_iff] at passed
 have count : a.accounts.length=7 := by simpa using passed.1.1
 obtain ⟨validated,_,_,_,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨acc0,_,_,index0,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨proofData,_,_,read0,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨acc6,_,_,index6,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨checkpointData,_,_,read6,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨_,_,_,_,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨_,_,_,lengthGuard,h,_⟩ := rsbind_return _ _ _ _ _ h
 have proofLength : proofData.length=AFTERSTATE_BYTES+validated.proof_length := by
  simpa using check_return _ _ _ _ lengthGuard
 obtain ⟨encoded,_,_,_,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨publicBytes,_,_,_,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨_,_,_,publicGuard,h,_⟩ := rsbind_return _ _ _ _ _ h
 have publicLength : publicBytes.length=STATEMENT_BYTES := by
  simpa using check_return _ _ _ _ publicGuard

 obtain ⟨verifyEvents,domain,verified⟩ := NNC_RSLAuth.call V publicBytes
  (slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+validated.proof_length)) checkpointData
  (L.emitResult validated.statement) env _ h
 refine ⟨{
  acc0 := acc0
  acc6 := acc6
  proofData := proofData
  checkpointData := checkpointData
  publicBytes := publicBytes
  n := validated.proof_length
  verifyEvents := verifyEvents
  count := count
  index0 := ?_
  index6 := ?_
  read0 := ?_
  read6 := ?_
  proofLength := proofLength
  publicLength := publicLength
  domain := domain
  verified := verified }⟩
 · exact index_return _ _ _ _ _ index0
 · exact index_return _ _ _ _ _ index6
 · exact ofExcept_return _ _ _ _ read0
 · exact ofExcept_return _ _ _ _ read6
#print axioms from_reference
end NNC_RSLReads
