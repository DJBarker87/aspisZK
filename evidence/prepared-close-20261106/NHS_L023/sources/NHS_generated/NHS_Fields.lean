import NHS_ProducedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_Fields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFN_LPi_FieldValues CheckpointBytes3Namespaces OraclePortCkptAbi4Decode

def QCanonical (x : aspis_core.field.QM31) : Prop :=
 x.c0.a.val<2147483647 ∧ x.c0.b.val<2147483647 ∧
 x.c1.a.val<2147483647 ∧ x.c1.b.val<2147483647

/-- Pure nominal layout transport. This lemma is not advertised as discharge
of its semantic alpha/coordinate inputs. The producer association is separate. -/
theorem transport (p : verifier.Prepared)
 (variant : p.variant=.S2)
 (queries : ∀ q∈p.queries.val,q.val<262144)
 (gamma : canonE (NFW_SampledDomains.toNative p.gamma))
 (kappa : canonE (NFW_SampledDomains.toNative p.kappa))
 (alpha : ∀ x∈p.alpha.val,canonE (NFW_SampledDomains.toNative x))
 (rho : NBF_PowerStep.Canonical (NFW_PreparedPort.prepared p).rho)
 (semanticAlpha : ∀ x∈p.semantic_alpha.val,QCanonical x)
 (coordinates : ∀ z∈p.z.val,QCanonical z.x ∧ QCanonical z.y)
 (claim : CanonicalWide (toE (NFW_PreparedPort.e p.claim))) :
 NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared p) := by
 constructor
 · change toVariant (NFW_PreparedPort.variant p.variant) = _
   rw [variant]
   rfl
 · intro j
   exact queries _ (List.getElem_mem _)
 · exact NHS_CanonicalPorts.wide p.gamma gamma
 · exact NHS_CanonicalPorts.wide p.kappa kappa
 · intro j
   simp only [toPrepared,NFW_PreparedPort.prepared,NFW_PreparedPort.map,mapArray,List.getElem_map]
   exact NHS_CanonicalPorts.wide _ (alpha _ (List.getElem_mem _))
 · exact rho
 · intro j
   simp only [toPrepared,NFW_PreparedPort.prepared,NFW_PreparedPort.map,mapArray,List.getElem_map]
   exact NHS_CanonicalPorts.qm _ (semanticAlpha _ (List.getElem_mem _))
 · intro j
   fin_cases j
   all_goals
     simp only [toPrepared,NFW_PreparedPort.prepared,NFW_PreparedPort.map,mapArray,List.getElem_map]
     first
     | exact NHS_CanonicalPorts.qm _ (coordinates _ (List.getElem_mem _)).1
     | exact NHS_CanonicalPorts.qm _ (coordinates _ (List.getElem_mem _)).2
 · exact claim
#print axioms transport
end AspisR1.NHS_Fields
