import R1Z.PV_RunJoin_CopyCertificate20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CertificateExecution20
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep

theorem last (c : Certificate)
    (hc : ∀ n, n < 11 → Canonical (c.states (n+1)))
    (hm : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1))) :
    (do let rounds ← R0PoseidonCopy.perm_rounds c.pre c.absorption
        ok rounds.val[10]!) = ok (c.states 11) := by
  obtain ⟨rounds,hr,hv⟩ := permutation c hc hm
  rw [hr]
  simp only [bind_tc_ok]
  rw [hv 10 (by decide)]
#print axioms last

theorem digest (c : Certificate)
    (hc : ∀ n, n < 11 → Canonical (c.states (n+1)))
    (hm : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1))) :
    blockDigestR c.pre c.absorption = ok (digest8 (c.states 11)) := by
  obtain ⟨rounds,hr,hv⟩ := permutation c hc hm
  rw [blockDigestR,hr]
  simp only [bind_tc_ok]
  rw [hv 10 (by decide)]
#print axioms digest

theorem sponge (c : Certificate)
    (hc : ∀ n, n < 11 → Canonical (c.states (n+1)))
    (hm : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1)))
    (chunk : Array U32 8#usize) (len : Usize)
    (ha : R0BlockCopies.sponge_absorb chunk len = ok c.absorption) :
    spongeStep c.pre chunk len = ok (c.states 11) := by
  rw [spongeStep,ha]
  simp only [bind_tc_ok]
  exact last c hc hm
#print axioms sponge
end R1Z.PV_RunJoin_CertificateExecution20
