import R1Z.ProverRwP7FibrePower
import R1Z.ProverRwP7FibreInstall
import R1Z.ProverRwP7ReverseControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibreTotal
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Src {E : Type} := @ProverRwP7FibreSource.aspis_core.r0.domain.fibre_point E

theorem reverse (i : aspis_core.r0.domain.FibreIndex) :
    ∃ n, ProverRwP7FibreSource.aspis_core.r0.domain.rev18 i = ok n := by
  unfold ProverRwP7FibreSource.aspis_core.r0.domain.rev18
  simp only [lift,bind_tc_ok,ProverRwP7FibreSource.core.num.U32.reverse_bits,
    ProverRwP7ReverseControl.source]
  exact ⟨_,rfl⟩

theorem source {E : Type} (field : aspis_core.r0.scalar.CodeField E)
    (embed : ∀ m, ∃ x, field.from_m31 m = ok x)
    (i : aspis_core.r0.domain.FibreIndex) : ∃ p, Src field i = ok p := by
  obtain ⟨n,hn⟩ := reverse i
  unfold Src ProverRwP7FibreSource.aspis_core.r0.domain.fibre_point
  simp only [ProverRwP7FibreSource.aspis_core.field.CM31.new,bind_tc_ok,hn,lift]
  apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP7FibrePower.total _ _ _)
  intro value
  obtain ⟨x,hx⟩ := embed value.a
  obtain ⟨y,hy⟩ := embed value.b
  exact ⟨⟨x,y⟩,by simp only [hx,hy,bind_tc_ok]⟩
#print axioms reverse
#print axioms source
end R1Z.ProverRwP7FibreTotal
