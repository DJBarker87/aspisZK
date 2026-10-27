import XRm_FieldValues
import XRm_FieldCanonical
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools XRm_Reduce XRm_FieldValues XRm_FieldCanonical
namespace XRm_ComplexValues
abbrev F := M31Exact
theorem reduce (x : U64) (out : U32)
    (run : XRk_Field.field.M31.reduce_u64 x=ok out) : (out.val:F)=(x.val:F) := by
  unfold XRk_Field.field.M31.reduce_u64 at run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact reduce_value _ _ hr

theorem sum_value (a b : U32) :
    (U64.wrapping_add (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val=a.val+b.val := by
  rw [U64.wrapping_add_val_eq,U32.cast_U64_val_eq,U32.cast_U64_val_eq,u64_size_eq]
  apply Nat.mod_eq_of_lt
  have ha : a.val<4294967296 := by scalar_tac
  have hb : b.val<4294967296 := by scalar_tac
  norm_num [u64Cardinality]
  omega

theorem cmul (a b out : aspis_core.field.CM31) (ha : C a) (hb : C b)
    (run : XRk_Field.field.CM31.mul a b=ok out) :
    (out.a.val:F)=(a.a.val:F)*(b.a.val:F)-(a.b.val:F)*(b.b.val:F) ∧
    (out.b.val:F)=(a.a.val:F)*(b.b.val:F)+(a.b.val:F)*(b.a.val:F) := by
  unfold XRk_Field.field.CM31.mul at run
  obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨z,hz,run⟩ := bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  obtain ⟨s,hs,run⟩ := bind_success _ _ _ run
  obtain ⟨t,ht,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  have cx := XRm_FieldCanonical.mul _ _ _ hx
  have cy := XRm_FieldCanonical.mul _ _ _ hy
  have cz := XRm_FieldCanonical.reduce _ _ hz
  have cs := XRm_M31Canonical.sub _ _ _ cz cx hs
  have vx := XRm_FieldValues.mul _ _ _ hx
  have vy := XRm_FieldValues.mul _ _ _ hy
  have vz := reduce _ _ hz
  have vr := XRm_FieldValues.sub _ _ _ cx cy hr
  have vs := XRm_FieldValues.sub _ _ _ cz cx hs
  have vt := XRm_FieldValues.sub _ _ _ cs cy ht
  have ba : a.a.val+a.b.val<4294967296 := by
    rcases ha with ⟨h0,h1⟩
    unfold M at h0 h1
    scalar_tac
  have bb : b.a.val+b.b.val<4294967296 := by
    rcases hb with ⟨h0,h1⟩
    unfold M at h0 h1
    scalar_tac
  have product := Nat.mul_lt_mul_of_lt_of_lt ba bb
  rw [U64.wrapping_mul_val_eq,sum_value,sum_value,u64_size_eq,
    show u64Cardinality=18446744073709551616 by norm_num [u64Cardinality],
    Nat.mod_eq_of_lt product,Nat.cast_mul,Nat.cast_add,Nat.cast_add] at vz
  constructor
  · exact vr.trans (by rw [vx,vy])
  · rw [vt,vs,vz,vx,vy]
    ring
#print axioms reduce
#print axioms sum_value
#print axioms cmul
end XRm_ComplexValues
