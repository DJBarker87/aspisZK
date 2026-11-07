import NNC_RSLAuth
import NNC_G1a
set_option autoImplicit false
namespace NNC_ReaderCut
open RSL RSL.TX2_241 RSL.TAS
/-- From an accepted verifier-call suffix of the weak reference, obtain the
matched header at EXACTLY those bytes. No native child Result or Root0 is
an input; every child fact follows from the complete accepted reference. -/
theorem matched (S : Sig) (L : PoolLib) (V0 : V2Lib) (VL : VLib)
 (I : Impl L V0 VL) (g : RSL.TAS.NNC_G1a S L V0 VL I)
 (pub proof ck : Bytes) (tail : RS Unit) (env : Env) (events : List Event)
 (run : RS.bind (RS.lift (Spec.call (Dom064 (lib V0 (fun _ _=>True) g.w))
  (fun x=>g.w x.1 x.2.1 x.2.2) (pub,proof,ck)))
  (fun r=>RS.seq (mapVErr (lib V0 (fun _ _=>True) g.w) r) tail)
  env ⟨.ret (.ok ()),events⟩) : S.readerHeader env pub proof ck := by
 obtain ⟨es,domain,law⟩ := NNC_RSLAuth.call (lib V0 (fun _ _=>True) g.w) pub proof ck tail env events run
 exact g.okHeader pub proof ck env ⟨.ret (.ok ()),es⟩ domain law rfl
#print axioms matched
end NNC_ReaderCut
