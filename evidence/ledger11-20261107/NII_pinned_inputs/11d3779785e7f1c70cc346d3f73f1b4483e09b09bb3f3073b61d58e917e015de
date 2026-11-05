import NGY_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Loop
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- ReadDomain and the SAME prestate invariant construct every child call and
thread its full logged poststate. No complete loop equality is a premise. -/
theorem from_invariant {H : Type} (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
 (point : Usize) (domain : NGU_LPq_PointConstruct.ReadDomain sem y1 g point)
 (iter : NGU_LPm_PointLoop.Range) (s : Native)
 (last : iter.end.val=29) (bound : iter.start.val≤29)
 (bounded : NGU_LPm_PublicFold.Bounded s iter.start.val) :
 ∃ xs out, NGU_LPm_PointLoop.Trace sem y1 g point iter s xs out ∧
  verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst iter sem y1 g point (statePort s)=
   ok (.Ok (ePort out)) := by
 obtain ⟨xs,out,tr⟩ := NGU_LPq_PointConstruct.loop sem y1 g point domain 29 iter s
  last bound (by omega) bounded
 exact ⟨xs,out,tr,NGU_LPm_PointLoop.source inst tr⟩

/-- The model-side G has exactly the selected child's poststate at each
constructed step, with all three native state fields retained. -/
theorem installed_step {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
 (g : Array Concrete.E 29#usize) (point lane : Usize)
 (domain : NGU_LPq_PointConstruct.ReadDomain sem y1 g point)
 (s : Native) (hl : lane.val<29) (bounded : NGU_LPm_PublicFold.Bounded s lane.val) :
 ∃ v q after, canonE v ∧ canonQ q ∧
  ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=ok (qPort q) ∧
  Array.index_usize g lane=ok (ePort v) ∧
  FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),after) ∧
  NGU_LPm_PublicFold.Bounded after (lane.val+1) ∧
  NGY_Oracle.reference lane.val s after v q (.Ok ())=
   (.advance (lane.val+1),after,[⟨v,q,s,after,.Ok ()⟩]) := by
 obtain ⟨q,cq,read⟩ := domain.1 lane hl
 obtain ⟨v,cv,weight⟩ := domain.2 lane hl
 obtain ⟨after,push,bnext,rest⟩ := NGU_LPm_PublicFold.step s v q lane.val hl bounded cv cq
 exact ⟨v,q,after,cv,cq,read,weight,push,bnext,rfl⟩

#print axioms from_invariant
#print axioms installed_step
end AspisR1.NGY_Loop
end
