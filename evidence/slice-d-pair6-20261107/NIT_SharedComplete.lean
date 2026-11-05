import NIT_SharedChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_SharedComplete
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIT_SharedChain
variable [FIo_Native.Allocation]

/-- No successful-partials or successful-high premise: split their complete
Results, and pass each actual post-state to the next cut. -/
theorem complete (c : Context) (parts : Parts)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 ∃ out,Shared c parts out ∧ shared c parts=out := by
 have cz : NHI_CellCanon.array (Array.repeat 16#usize NHX_FilledZero.zeroQ) := by
  intro q hq
  simp only [Array.repeat,List.mem_replicate] at hq
  exact hq.2 ▸ NHX_FilledZero.zero_canonical
 obtain ⟨⟨owner,cells⟩,trace,source,same,cc⟩ := NIT_CommonChain.complete c.w.value domain.factors
  (Array.repeat 16#usize NHX_FilledZero.zeroQ) cz
 dsimp only at same
 subst owner
 have result : ∃ out,Shared c parts out := by
  cases call : FIo_Native.weights.shared_partials c.f.value cells with
  | fail e => exact ⟨fail e,.failed c.w.value cells e trace call⟩
  | div => exact ⟨div,.diverged c.w.value cells trace call⟩
  | ok reply =>
   obtain ⟨out,tail⟩ := partial_exists c c.w parts reply domain.s2
    (NIT_PairDomain.message_size _ _ _ _ domain) domain.factors domain.extra c0 c1 cp domain.kappa
   exact ⟨out,.returned c.w.value cells reply out trace call tail⟩
 obtain ⟨out,trace⟩ := result
 exact ⟨out,trace,shared_interpreted c parts out domain trace⟩

#print axioms complete
end AspisR1.NIT_SharedComplete
