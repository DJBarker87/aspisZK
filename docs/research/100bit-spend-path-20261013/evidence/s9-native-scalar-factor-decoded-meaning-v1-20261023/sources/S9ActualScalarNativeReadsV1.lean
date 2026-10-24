import S9ActualScalarFourTermMeaningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualScalarNativeReadsV1
open AspisR1S9ActualPairScalarCallbackV1
open AspisR1S9ActualScalarFourTermMeaningV1
abbrev E := AspisWideTower.WideExact
abbrev nativeTerm (p : W) (q : Q) : E :=
  AspisR1S9ScalarFactorFourFoldMeaningV1.contribution (toHelperW p) (toHelperQ q)

theorem native_perm_eq_helper : AspisR1S9ProductionPairCutV1.weights.PERM=
    AspisR1S9HelperP6.weights.PERM := by
  unfold AspisR1S9ProductionPairCutV1.weights.PERM AspisR1S9HelperP6.weights.PERM
  rfl

theorem native_quarter_eq_helper : AspisR1S9ProductionPairCutV1.weights.QUARTER=
    AspisR1S9HelperP6.weights.QUARTER := by
  unfold AspisR1S9ProductionPairCutV1.weights.QUARTER AspisR1S9HelperP6.weights.QUARTER
  rfl

/-- The actual source PERM is [0,3,2,1]. All eight source reads and the
quarter-scaled value come from this SAME accepted native scalar call. -/
theorem actual_scalar_success_native_reads_quarter
    (f : Array Q 4#usize) (p : Array W 4#usize) (out : W)
    (hp : GoodArray p) (hf : GoodQArray f)
    (hcall : AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f p=.ok out) :
    Canonical out ∧ ∃ (p0 p1 p2 p3 : W) (q0 q1 q2 q3 : Q),
      Array.index_usize p 0#usize=.ok p0 ∧ Array.index_usize f 0#usize=.ok q0 ∧
      Array.index_usize p 3#usize=.ok p1 ∧ Array.index_usize f 1#usize=.ok q1 ∧
      Array.index_usize p 2#usize=.ok p2 ∧ Array.index_usize f 2#usize=.ok q2 ∧
      Array.index_usize p 1#usize=.ok p3 ∧ Array.index_usize f 3#usize=.ok q3 ∧
      decodeNative out = (((((0 : E)+nativeTerm p0 q0)+nativeTerm p1 q1)+
        nativeTerm p2 q2)+nativeTerm p3 q3)*
        AspisR1CurrentWide.Proof.wideScalarEmbedding
          AspisR1S9ProductionPairCutV1.weights.QUARTER := by
  have hout := (AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps
    f p out hp hcall).1
  obtain ⟨we,j0,j1,j2,j3,pv0,pv1,pv2,pv3,qv0,qv1,qv2,qv3,
      hwe,hperm0,hp0,hq0,hperm1,hp1,hq1,hperm2,hp2,hq2,hperm3,hp3,hq3,hmeaning⟩ :=
    actual_scalar_success_four_term_meaning f p out hp hf hcall
  obtain ⟨perm0,perm1,perm2,perm3⟩ := AspisR1S9TransparentFoldS2InstanceV1.perm_reads
  have ej0 : j0=0#usize := Result.ok.inj (hperm0.symm.trans perm0)
  have ej1 : j1=3#usize := Result.ok.inj (hperm1.symm.trans perm1)
  have ej2 : j2=2#usize := Result.ok.inj (hperm2.symm.trans perm2)
  have ej3 : j3=1#usize := Result.ok.inj (hperm3.symm.trans perm3)
  subst j0; subst j1; subst j2; subst j3
  obtain ⟨p0,rp0,ep0⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperW p 0#usize pv0 hp0
  obtain ⟨p1,rp1,ep1⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperW p 3#usize pv1 hp1
  obtain ⟨p2,rp2,ep2⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperW p 2#usize pv2 hp2
  obtain ⟨p3,rp3,ep3⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperW p 1#usize pv3 hp3
  obtain ⟨q0,rq0,eq0⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperQ f 0#usize qv0 hq0
  obtain ⟨q1,rq1,eq1⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperQ f 1#usize qv1 hq1
  obtain ⟨q2,rq2,eq2⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperQ f 2#usize qv2 hq2
  obtain ⟨q3,rq3,eq3⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv toHelperQ f 3#usize qv3 hq3
  rw [←ep0,←ep1,←ep2,←ep3,←eq0,←eq1,←eq2,←eq3,←native_quarter_eq_helper] at hmeaning
  exact ⟨hout,p0,p1,p2,p3,q0,q1,q2,q3,rp0,rq0,rp1,rq1,rp2,rq2,rp3,rq3,hmeaning⟩

#print axioms native_perm_eq_helper
#print axioms native_quarter_eq_helper
#print axioms actual_scalar_success_native_reads_quarter
end AspisR1S9ActualScalarNativeReadsV1
