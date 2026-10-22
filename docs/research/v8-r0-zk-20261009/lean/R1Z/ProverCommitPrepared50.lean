import R1Z.ProverCommitPreparedCM50
/-! Actual prepared constructor and QM31 multiplication value, retaining
canonicality and input representation explicitly. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPrepared50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitChannelAlgebra49 (components cmComponents)

def matrix (a : Nat → Nat → U32) :=
  ProverCommitArray49.array 3#usize (fun i => ProverCommitArray49.array 3#usize (a i))

theorem prepare_eq (x : Old.Q) (hx : Canonical x) :
    prepared50.prepare (ProverCommitNativeQ48.source x)=dot50.prepare (ProverCommitNativeQ48.source x) := by
  obtain ⟨s,hs,hcs,hvs⟩ := ProverCommitNativeC49.add x.c0 x.c1 hx.1 hx.2
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitPrepare50.cm x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitPrepare50.cm x.c1 hx.2
  obtain ⟨c,hc,hcc,hvc⟩ := ProverCommitPrepare50.cm s hcs
  change (do
    let a ← dot50.prepare_c (ProverCommitNativeC49.source x.c0)
    let b ← dot50.prepare_c (ProverCommitNativeC49.source x.c1)
    let s ← field.CM31.add (ProverCommitNativeC49.source x.c0) (ProverCommitNativeC49.source x.c1)
    let c ← dot50.prepare_c s
    ok (Array.make 3#usize [a,b,c]))=(do
    let s ← field.CM31.add (ProverCommitNativeC49.source x.c0) (ProverCommitNativeC49.source x.c1)
    let a ← dot50.prepare_c (ProverCommitNativeC49.source x.c0)
    let b ← dot50.prepare_c (ProverCommitNativeC49.source x.c1)
    let c ← dot50.prepare_c s
    ok (Array.make 3#usize [a,b,c]))
  simp only [hs,ha,hb,hc,bind_tc_ok]

theorem prepare (x : Old.Q) (hx : Canonical x) :
    ∃ a : Nat → Nat → U32, prepared50.prepare (ProverCommitNativeQ48.source x)=ok (matrix a) ∧
      (∀ i j, i<3 → j<3 → (a i j).val<AspisCircleGroupOrder.P) ∧
      (∀ i j : Fin 3, ((a i.val j.val).val : M31Exact)=components (decode x) i j) := by
  rw [prepare_eq x hx]
  exact ProverCommitPrepare50.q x hx

theorem combine (a b c : Old.C)
    (ha : ProverCommitNativeC49.Canonical a) (hb : ProverCommitNativeC49.Canonical b)
    (hc : ProverCommitNativeC49.Canonical c) :
    ∃ z : Old.Q, prepared50.combine (ProverCommitNativeC49.source a) (ProverCommitNativeC49.source b)
      (ProverCommitNativeC49.source c)=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=⟨ProverCommitNativeC49.value a+qm31R*ProverCommitNativeC49.value b,
        ProverCommitNativeC49.value c-ProverCommitNativeC49.value a-ProverCommitNativeC49.value b⟩ := by
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitNativeC49.mul_r b hb
  have hr' : reconstruction.mul_r (ProverCommitNativeC49.source b)=ok (ProverCommitNativeC49.source r) := hr
  obtain ⟨lo,hlo,hclo,hvlo⟩ := ProverCommitNativeC49.add a r ha hcr
  obtain ⟨t,ht,hct,hvt⟩ := ProverCommitNativeC49.sub c a hc ha
  obtain ⟨hi,hhi,hchi,hvhi⟩ := ProverCommitNativeC49.sub t b hct hb
  refine ⟨⟨lo,hi⟩,?_,⟨hclo,hchi⟩,?_⟩
  · simp only [prepared50.combine,hr',hlo,ht,hhi,bind_tc_ok];rfl
  · apply QuadraticAlgebra.ext
    · change ProverCommitNativeC49.value lo=_
      rw [hvlo,hvr]
    · change ProverCommitNativeC49.value hi=_
      rw [hvhi,hvt]

theorem karatsuba (x y : QM31Exact) :
    (⟨x.re*y.re+qm31R*(x.im*y.im),
      (x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩ : QM31Exact)=x*y := by
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

theorem mul (a : Nat → Nat → U32) (x : QM31Exact) (y : Old.Q)
    (hy : Canonical y)
    (ha : ∀ i j : Fin 3, ((a i.val j.val).val : M31Exact)=components x i j) :
    ∃ z : Old.Q, prepared50.mul (matrix a) (ProverCommitNativeQ48.source y)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=x*decode y := by
  obtain ⟨s,hs,hcs,hvs⟩ := ProverCommitNativeC49.add y.c0 y.c1 hy.1 hy.2
  obtain ⟨m0,hm0,hc0,hv0⟩ := ProverCommitPreparedCM50.cm (a 0) x.re y.c0 hy.1 (ha 0)
  obtain ⟨m1,hm1,hc1,hv1⟩ := ProverCommitPreparedCM50.cm (a 1) x.im y.c1 hy.2 (ha 1)
  obtain ⟨m2,hm2,hc2,hv2⟩ := ProverCommitPreparedCM50.cm (a 2) (x.re+x.im) s hcs (ha 2)
  obtain ⟨z,hz,hcz,hdz⟩ := combine m0 m1 m2 hc0 hc1 hc2
  refine ⟨z,?_,hcz,?_⟩
  · change (do
      let a0 ← Array.index_usize (matrix a) 0#usize
      let m0 ← prepared50.cm a0 (ProverCommitNativeC49.source y.c0)
      let a1 ← Array.index_usize (matrix a) 1#usize
      let m1 ← prepared50.cm a1 (ProverCommitNativeC49.source y.c1)
      let a2 ← Array.index_usize (matrix a) 2#usize
      let s ← field.CM31.add (ProverCommitNativeC49.source y.c0) (ProverCommitNativeC49.source y.c1)
      let m2 ← prepared50.cm a2 s
      prepared50.combine m0 m1 m2)=_
    simp only [matrix,ProverCommitArray49.index 3#usize _ 0#usize (by decide),
      ProverCommitArray49.index 3#usize _ 1#usize (by decide),
      ProverCommitArray49.index 3#usize _ 2#usize (by decide),
      show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,show (2#usize).val=2 from rfl,
      hm0,hm1,hs,hm2,hz,bind_tc_ok]
  · rw [hdz,hv0,hv1,hv2,hvs]
    exact karatsuba x (decode y)

theorem caller (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, (do
      let a ← prepared50.prepare (ProverCommitNativeQ48.source x)
      prepared50.mul a (ProverCommitNativeQ48.source y))=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨a,ha,hca,hva⟩ := prepare x hx
  obtain ⟨z,hz,hcz,hdz⟩ := mul a (decode x) y hy hva
  exact ⟨z,by rw [ha];exact hz,hcz,hdz⟩

#print axioms prepare_eq
#print axioms prepare
#print axioms combine
#print axioms karatsuba
#print axioms mul
#print axioms caller
end R1Z.ProverCommitPrepared50
