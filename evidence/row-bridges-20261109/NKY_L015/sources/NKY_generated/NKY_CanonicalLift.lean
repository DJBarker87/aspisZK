import NKY_LevelCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_CanonicalLift
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev M := AspisV8R15.ExactTowerBase.M31Exact

def word (x : M) : U32 := UScalar.ofNatCore x.val (by
 have h:=ZMod.val_lt x
 change x.val<2147483647 at h
 scalar_tac)
def encode (x : K) : NQ :=
 ⟨⟨word x.re.re,word x.re.im⟩,⟨word x.im.re,word x.im.im⟩⟩

theorem canonical (x : K) : Canon (encode x) := by
 exact ⟨⟨ZMod.val_lt x.re.re,ZMod.val_lt x.re.im⟩,
  ⟨ZMod.val_lt x.im.re,ZMod.val_lt x.im.im⟩⟩

theorem decode_encode (x : K) : decode (encode x)=x := by
 cases x with
 | mk re im =>
  cases re
  cases im
  simp [encode,word,FIv_NativeValue.decode,FIv_NativeArithmetic.qm,
   FIv_NativeArithmetic.cm,ExtractedMaskQM31Exact.decode]

theorem encode_decode (x : NQ) (hx : Canon x) : encode (decode x)=x := by
 apply NJB_DecodeInjective.qm _ _ (canonical _) hx
 exact decode_encode _

/-- Canonical literal pair associated to the adopted four-cell value model.
It is independent of the native result or the frame interpreter. -/
def cohort (index : U64) (f : NJX_AppendDomains.Frontier) (o : NJX_DigestCohort.O)
 (s : NJX_AppendDomains.High) (p : NKI_LevelsChildren.Family index f o s) : NKY_LevelCarrier.Pair :=
 NKY_LevelCarrier.pair (fun j=>encode (NKI_LevelsCohort.model index f o s p j))

theorem result (index : U64) (f : NJX_AppendDomains.Frontier) (o : NJX_DigestCohort.O)
 (s : NJX_AppendDomains.High) (p : NKI_LevelsChildren.Family index f o s)
 (out : NJX_AppendFold.State) (hc : ∀ j,Canon (out j))
 (hv : ∀ j,decode (out j)=NKI_LevelsCohort.model index f o s p j) :
 NKY_LevelCarrier.pair out=cohort index f o s p := by
 apply congrArg NKY_LevelCarrier.pair
 funext j
 exact (NJB_DecodeInjective.qm _ _ (hc j) (canonical _) ((hv j).trans (decode_encode _).symm))
#print axioms canonical
#print axioms decode_encode
#print axioms encode_decode
#print axioms result
end AspisR1.NKY_CanonicalLift
end
