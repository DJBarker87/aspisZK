import LPm_DotPort
set_option autoImplicit false
namespace AspisR1.LPm_PublicPort
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort LPm_UpdatePort

 theorem raw_values_injective (x y : LPm_PublicState.Raw)
    (same : LPm_PublicState.values x=LPm_PublicState.values y) : x=y := by
  obtain ⟨a,b,c,d,hx⟩ := LPf_ArrayFour.shape x
  obtain ⟨e,f,g,h,hy⟩ := LPf_ArrayFour.shape y
  subst x; subst y
  simp only [LPm_PublicState.values,Array.make,List.getElem!_cons_zero,
    List.getElem!_cons_succ,Prod.mk.injEq] at same
  rcases same with ⟨ha,hb,hc,hd⟩
  simp only [UScalar.eq_of_val_eq ha,UScalar.eq_of_val_eq hb,
    UScalar.eq_of_val_eq hc,UScalar.eq_of_val_eq hd]

theorem raw_meaning (a b : LPi_RawValues.Q) (ha : LPi_RawValues.Canon a)
    (hb : LPi_RawValues.Canon b) (r : LPm_PublicState.Raw)
    (call : FIo_Native.fast_pairing.canonical.Q.raw a b=ok r) :
    LPm_PublicState.values r=LPi_RawValues.spec a b := by
  obtain ⟨r0,r1,r2,r3,actual,meaning⟩ := LPi_RawValues.source a b ha hb
  have unique := Result.ok.inj (call.symm.trans actual)
  rw [unique]
  exact meaning

theorem state_ext (x y : State) (lo : x.c0.sums=y.c0.sums)
    (hi : x.c1.sums=y.c1.sums) (count : x.count=y.count) : x=y := by
  rcases x with ⟨⟨a⟩,⟨b⟩,c⟩
  rcases y with ⟨⟨d⟩,⟨e⟩,f⟩
  simp_all only

/-- The concrete native public step and the retained concrete cohort step
return the SAME complete eight-word state. All call/value observations are
derived from their total source theorems, not supplied as whole step equality. -/
theorem source (s : Native) (v : NE) (q : NQ)
    (hv : canonE v) (hq : canonQ q) (count : s.count.val<4096) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧
      AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
        (statePort s) (AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v))
        (AspisR1S5ClaimDotConcreteAdapter.toPushQm (qPort q))=ok (.Ok (),statePort out) := by
  let vm := AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v)
  let qm := AspisR1S5ClaimDotConcreteAdapter.toPushQm (qPort q)
  have cv : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical vm := hv
  have cc : (statePort s).count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    simp only [statePort,AspisR1EbyKPushExplicitOpsV1.maxTerms]
    scalar_tac
  have cq : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ qm).val,x.val<2147483647 := by
    intro x hx
    simp only [qm,AspisR1EbyKPushDotBackend.scalarQ,
      AspisR1S5ClaimDotConcreteAdapter.toPushQm,qPort,Array.make,
      List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact hq.1.1
    · exact hq.1.2
    · exact hq.2.1
    · exact hq.2.2
  obtain ⟨lo,hi,out,ncall,lv,hv0,h0,h1,inc⟩ := LPm_PublicState.source s v q hv hq count
  obtain ⟨model,mcall⟩ := AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
    (statePort s) vm qm cv cc cq
  obtain ⟨ml,mr,mlcall,mrcall,mlsum,mrsum,_,minc,_⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend
      AspisR1EbyKPushDecodedProductUpdate.QRaw (statePort s) vm qm model mcall
  change AspisR1EbyKPushDecodedProductUpdate.QRaw (LPi_CheckedInputs.q v.c0)
    (LPi_CheckedInputs.q q)=ok ml at mlcall
  change AspisR1EbyKPushDecodedProductUpdate.QRaw (LPi_CheckedInputs.q v.c1)
    (LPi_CheckedInputs.q q)=ok mr at mrcall
  rw [raw_eq] at mlcall mrcall
  have mlval := raw_meaning _ _ (LPi_CheckedInputs.canonical v.c0 hv.1)
    (LPi_CheckedInputs.canonical q hq) ml mlcall
  have mrval := raw_meaning _ _ (LPi_CheckedInputs.canonical v.c1 hv.2)
    (LPi_CheckedInputs.canonical q hq) mr mrcall
  have mleq := raw_values_injective ml lo (mlval.trans lv.symm)
  have mreq := raw_values_injective mr hi (mrval.trans hv0.symm)
  subst ml; subst mr
  have loeq : model.c0.sums=(statePort out).c0.sums := by
    change model.c0.sums=out.c0.sums
    rw [mlsum,h0]
    exact (sums s.c0 lo).symm
  have hieq : model.c1.sums=(statePort out).c1.sums := by
    change model.c1.sums=out.c1.sums
    rw [mrsum,h1]
    exact (sums s.c1 hi).symm
  have ceq : model.count=(statePort out).count := UScalar.eq_of_val_eq (minc.trans inc.symm)
  have same := state_ext model (statePort out) loeq hieq ceq
  rw [same] at mcall
  exact ⟨out,ncall,mcall⟩

#print axioms raw_values_injective
#print axioms raw_meaning
#print axioms state_ext
#print axioms source
end AspisR1.LPm_PublicPort
