import R1Z.PV_RunJoin_AfterstateAgreement32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicAgreement32
open PV_Src_NativeInput PV_RunJoin_HonestIdentification26
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Full raw request header, including pool/domain/sequence and withdrawal
 destination. No equality of this header is inferred from semantic projection. -/
def header (i : Input) : Sum BuilderPublicProjection.Transfer BuilderPublicProjection.Withdrawal :=
  match i.request with
  | .transfer p _ => .inl p
  | .withdrawal p => .inr p

theorem raw (base : ProverRwFull.ExternalTypes) (a b : Input)
    (hh : header a=header b)
    (ht : a.compiled.public_statement=b.compiled.public_statement) :
    PV_RunJoin_NominalPublicData.fromInput base a=PV_RunJoin_NominalPublicData.fromInput base b := by
  cases a with
  | mk ar aw ac al snapA ap =>
    cases b with
    | mk br bw bc bl bs bp =>
      cases ar <;> cases br <;> cases hh
      all_goals simp only [PV_RunJoin_NominalPublicData.fromInput]
      all_goals rw [ht]
#print axioms raw

theorem honest (base : ProverRwFull.ExternalTypes) (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (hh : header a.val=header b.val)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain) :
    PV_RunJoin_NominalPublicData.fromInput base a.val=PV_RunJoin_NominalPublicData.fromInput base b.val :=
  raw base a.val b.val hh (PV_RunJoin_AfterstateAgreement32.transition a b same pool domain)
#print axioms honest
end R1Z.PV_RunJoin_PublicAgreement32
