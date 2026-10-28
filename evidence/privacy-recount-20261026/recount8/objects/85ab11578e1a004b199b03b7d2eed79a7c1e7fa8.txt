import R1Z.BuilderSpendRelation
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OutputPairMeaning31
open R0P R0Z.BuilderModel R1Z.BuilderSemanticBridge
open AspisR1 AspisR1.SpendRelation
variable {K : Type} [Field K] [DecidableEq K] [CharP K 2147483647]

theorem output (pub : Public K) (w : Witness K)
    (hchange : pub.change = changeCommitment pub w)
    (hout : variantOutput pub w) :
    outputPair pub = some (outPair pub (BuilderSpendRelation.modelWitness w)) := by
  cases hv : pub.variant
  · unfold variantOutput at hout
    rw [hv] at hout
    unfold outputPair outPair outPairB
    rw [hv,hout,Option.map_some,nodeDigest_eq pub (BuilderSpendRelation.modelWitness w),
      recipientDigest_eq pub (BuilderSpendRelation.modelWitness w) hv,
      changeDigest_eq pub (BuilderSpendRelation.modelWitness w),hchange]
    rfl
  · unfold outputPair outPair outPairB
    rw [hv,nodeDigest_eq pub (BuilderSpendRelation.modelWitness w),
      changeDigest_eq pub (BuilderSpendRelation.modelWitness w),hchange]
    rfl
#print axioms output
end R1Z.PV_RunJoin_OutputPairMeaning31
