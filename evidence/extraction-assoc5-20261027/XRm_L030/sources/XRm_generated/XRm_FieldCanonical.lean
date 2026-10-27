import XRm_M31Canonical
import XRm_Reduce
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRm_FieldCanonical
abbrev M (x : U32) := x<2147483647#u32
def C (x : aspis_core.field.CM31) : Prop := M x.a ∧ M x.b
def Q (x : aspis_core.field.QM31) : Prop := C x.c0 ∧ C x.c1

theorem mul (a b out : U32) (run : XRk_Field.field.M31.mul a b=ok out) : M out := by
  unfold XRk_Field.field.M31.mul at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact XRm_Reduce.canonical _ _ hr

theorem reduce (x : U64) (out : U32)
    (run : XRk_Field.field.M31.reduce_u64 x=ok out) : M out := by
  unfold XRk_Field.field.M31.reduce_u64 at run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact XRm_Reduce.canonical _ _ hr

theorem cadd (a b out : aspis_core.field.CM31) (ha : C a) (hb : C b)
    (run : XRk_Field.field.CM31.add a b=ok out) : C out := by
  unfold XRk_Field.field.CM31.add at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨XRm_M31Canonical.add _ _ _ ha.1 hb.1 hx,XRm_M31Canonical.add _ _ _ ha.2 hb.2 hy⟩

theorem csub (a b out : aspis_core.field.CM31) (ha : C a) (hb : C b)
    (run : XRk_Field.field.CM31.sub a b=ok out) : C out := by
  unfold XRk_Field.field.CM31.sub at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨XRm_M31Canonical.sub _ _ _ ha.1 hb.1 hx,XRm_M31Canonical.sub _ _ _ ha.2 hb.2 hy⟩

/-- Full-u64 reduction makes the multiplication output canonical even for
raw carriers. This does not assert raw inputs are canonical. -/
theorem cmul (a b out : aspis_core.field.CM31)
    (run : XRk_Field.field.CM31.mul a b=ok out) : C out := by
  unfold XRk_Field.field.CM31.mul at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨z,hz,run⟩ := bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  obtain ⟨s,hs,run⟩ := bind_success _ _ _ run
  obtain ⟨t,ht,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  have cx := mul _ _ _ hx
  have cy := mul _ _ _ hy
  have cz := reduce _ _ hz
  exact ⟨XRm_M31Canonical.sub _ _ _ cx cy hr,
    XRm_M31Canonical.sub _ _ _ (XRm_M31Canonical.sub _ _ _ cz cx hs) cy ht⟩

theorem qadd (a b out : aspis_core.field.QM31) (ha : Q a) (hb : Q b)
    (run : XRk_Field.field.QM31.add a b=ok out) : Q out := by
  unfold XRk_Field.field.QM31.add at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨cadd _ _ _ ha.1 hb.1 hx,cadd _ _ _ ha.2 hb.2 hy⟩

theorem qsub (a b out : aspis_core.field.QM31) (ha : Q a) (hb : Q b)
    (run : XRk_Field.field.QM31.sub a b=ok out) : Q out := by
  unfold XRk_Field.field.QM31.sub at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨csub _ _ _ ha.1 hb.1 hx,csub _ _ _ ha.2 hb.2 hy⟩

theorem mul_by_r (a out : aspis_core.field.CM31) (ha : C a)
    (run : XRk_Field.field.mul_by_r a=ok out) : C out := by
  unfold XRk_Field.field.mul_by_r at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  obtain ⟨z,hz,run⟩ := bind_success _ _ _ run
  obtain ⟨t,ht,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨XRm_M31Canonical.sub _ _ _ (XRm_M31Canonical.add _ _ _ ha.1 ha.1 hx) ha.2 hy,
    XRm_M31Canonical.add _ _ _ ha.1 (XRm_M31Canonical.add _ _ _ ha.2 ha.2 hz) ht⟩

theorem qmul (a b out : aspis_core.field.QM31) (ha : Q a) (hb : Q b)
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

#print axioms qmul
#print axioms mul
#print axioms reduce
#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms qadd
#print axioms qsub
#print axioms mul_by_r
end XRm_FieldCanonical
