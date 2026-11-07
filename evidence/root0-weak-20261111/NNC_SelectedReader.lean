import NNC_RSLReads
import NNC_G1a
set_option autoImplicit false
namespace NNC_SelectedReader
open RSL RSL.TX2_241 RSL.TAS
/-- The accepted call's Dom064 and exact selected range fix the original
proof account extent. No scanner Result or assumed57607 endpoint is needed. -/
theorem extent (V : V2Lib) (a : Args) (env : Env) (c : NNC_RSLReads.Cut V a env) :
 c.n=57607 ∧ c.proofData.length=58295 := by
 have length := c.domain.1
 simp only [PROOF_BYTES] at length
 have suffix : (slice c.proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+c.n)).length=c.n := by
  simp only [slice,List.length_take,List.length_drop,c.proofLength,Nat.add_sub_cancel_left,Nat.min_self]
 rw [suffix] at length
 have n : c.n=57607 := length
 exact ⟨n,by simpa only [n,AFTERSTATE_BYTES] using c.proofLength⟩

/-- Full accepted241 reference -> SAME read/index/range cuts plus matched
header under G1a. This is the Root0-free reader half of G1c. It consumes no
native2=model equation and no accepted2 or canonical064 law. -/
theorem from_reference (S : Sig) (L : PoolLib) (D : DeployedIds)
 (V0 : V2Lib) (VL : VLib) (I : Impl L V0 VL)
 (g : RSL.TAS.NNC_G1a S L V0 VL I) (a : Args) (env : Env) (events : List Event)
 (run : Ref L D (lib V0 (fun _ _=>True) g.w) a env ⟨.ret (.ok ()),events⟩) :
 ∃ c : NNC_RSLReads.Cut (lib V0 (fun _ _=>True) g.w) a env,
  c.n=57607 ∧ c.proofData.length=58295 ∧
  S.readerHeader env c.publicBytes (slice c.proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES) c.checkpointData := by
 obtain ⟨c⟩ := NNC_RSLReads.from_reference L D (lib V0 (fun _ _=>True) g.w) a env events run
 obtain ⟨n,len⟩ := extent _ a env c
 have header := g.okHeader c.publicBytes (slice c.proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+c.n))
  c.checkpointData env ⟨.ret (.ok ()),c.verifyEvents⟩ c.domain c.verified rfl
 refine ⟨c,n,len,?_⟩
 simpa only [n,AFTERSTATE_BYTES,PROOF_ACCOUNT_BYTES,PROOF_BYTES] using header
#print axioms extent
#print axioms from_reference
end NNC_SelectedReader
