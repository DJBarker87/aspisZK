import XRm_FieldCanonical
import XRk_FieldExternal
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools XRm_FieldCanonical
namespace XRm_WideProducer
theorem qmul_raw (a b out : aspis_core.field.QM31)
    (run : XRk_Field.field.QM31.mul a b=ok out) : Q out := by
  unfold XRk_Field.field.QM31.mul at run
  obtain ⟨m0,h0,run⟩ := bind_success _ _ _ run
  obtain ⟨m1,h1,run⟩ := bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := bind_success _ _ _ run
  obtain ⟨m2,h2,run⟩ := bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  obtain ⟨z,hz,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  have h0c := cmul _ _ _ h0
  have h1c := cmul _ _ _ h1
  have h2c := cmul _ _ _ h2
  exact ⟨cadd _ _ _ h0c (mul_by_r _ _ h1c hr) hx,
    csub _ _ _ (csub _ _ _ h2c h0c hy) h1c hz⟩


def Canonical (e : XRk_Wide) : Prop := Q (newQ e.c0) ∧ Q (newQ e.c1)

theorem mul_u (x out : aspis_core.field.QM31) (hx : Q x)
    (run : XRk_Field.field.wide_exact.mul_u x=ok out) : Q out := by
  unfold XRk_Field.field.wide_exact.mul_u at run
  obtain ⟨c,hc,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨mul_by_r _ _ hx.2 hc,hx.1⟩

/-- Canonical output of the actual wide-multiply producer, for arbitrary
extracted input carriers. No canonical-input hypothesis is added. -/
theorem mul (a b out : XRk_Wide)
    (run : aspis_core.field.wide_exact.WideExact.mul a b=ok out) : Canonical out := by
  unfold aspis_core.field.wide_exact.WideExact.mul at run
  obtain ⟨ac,hac,run⟩ := bind_success _ _ _ run
  obtain ⟨bd,hbd,run⟩ := bind_success _ _ _ run
  obtain ⟨aa,haa,run⟩ := bind_success _ _ _ run
  obtain ⟨bb,hbb,run⟩ := bind_success _ _ _ run
  obtain ⟨cross,hcross,run⟩ := bind_success _ _ _ run
  obtain ⟨u,hu,run⟩ := bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := bind_success _ _ _ run
  obtain ⟨e,he,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  have ca := qmul_raw _ _ _ hac
  have cb := qmul_raw _ _ _ hbd
  have cc := qmul_raw _ _ _ hcross
  exact ⟨qadd _ _ _ ca (mul_u _ _ cb hu) hc,
    qsub _ _ _ (qsub _ _ _ cc ca hd) cb he⟩

theorem one : Canonical (⟨oldQ qone,oldQ qzero⟩ : XRk_Wide) := by
  unfold Canonical Q C M
  repeat constructor <;> scalar_tac

theorem zero : Canonical (⟨oldQ qzero,oldQ qzero⟩ : XRk_Wide) := by
  unfold Canonical Q C M
  repeat constructor <;> scalar_tac
#print axioms qmul_raw
#print axioms mul_u
#print axioms mul
#print axioms one
#print axioms zero
end XRm_WideProducer
