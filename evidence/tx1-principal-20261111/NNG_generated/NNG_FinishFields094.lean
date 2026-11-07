import NNG_ModelHead136
import NHS_SemanticFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishFields094
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
/-- The installed CLOSED semantic finish derives canonical copied alpha and
circle coordinates on its SAME emitted returned arm. No independent semantic
finish witness or point-canonicality premise is added. -/
theorem returned {W : Type} (env : RSL.Env) (s : Parent Unit W)
 (out : r1_semantic.Verified Unit)
 (native : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out)) :
 (∀ q∈(toT11 out).alpha.val,NHS_Fields.QCanonical q) ∧
 (∀ z∈(toT11 out).z.val,NHS_Fields.QCanonical z.x ∧ NHS_Fields.QCanonical z.y) := by
 have model := NNG_ModelSuccess136.finish env s out native
 have installed : F3M_CircleSource.install (NNG_LegacyConfig136.boundaries env)=
  NNG_LegacyConfig136.boundaries env := rfl
 rw [←installed] at model
 exact NHS_SemanticFields.source AspisS1ExtractedRoundChildren.children (NNG_LegacyConfig136.boundaries env)
  (NNG_Install.digest s.digest) (toT9 s.publicValue) (toT12 s.prefixValue) (toT10 s.transcript)
  (toT3 s.challenges) none (toT11 out) model
#print axioms returned
end AspisR1.NNG_FinishFields094
