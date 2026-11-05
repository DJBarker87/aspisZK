import NIT_Cuts
import NHM_EEncoding
set_option autoImplicit false
namespace AspisR1.NIT_FieldInterpretation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

theorem cw_injective : Function.Injective cw := by
 intro x y h
 have a := UScalar.eq_of_val_eq (congrArg Prod.fst h)
 have b := UScalar.eq_of_val_eq (congrArg Prod.snd h)
 cases x; cases y; cases a; cases b; rfl

theorem qw_injective : Function.Injective qw := by
 intro x y h
 have a := cw_injective (congrArg Prod.fst h)
 have b := cw_injective (congrArg Prod.snd h)
 cases x; cases y; cases a; cases b; rfl

theorem ew_injective : Function.Injective ew := by
 intro x y h
 have a := qw_injective (congrArg Prod.fst h)
 have b := qw_injective (congrArg Prod.snd h)
 cases x; cases y; cases a; cases b; rfl

/-- Individual field stub laws, never an enclosing pair-output premise. -/
def QMul (a b reply : K) : Prop := qw reply=mulQ (qw a) (qw b)
def EMul (a b reply : E) : Prop := ew reply=mulE (ew a) (ew b)
def EAdd (a b reply : E) : Prop :=
 ew reply=(addQ (qw a.c0) (qw b.c0),addQ (qw a.c1) (qw b.c1))

theorem qm (a b reply : K) (ha : canonQ a) (hb : canonQ b)
 (law : QMul a b reply) :
 FIo_Native.aspis_core.field.QM31.mul a b=ok reply ∧ canonQ reply := by
 obtain ⟨out,run,canonical,value⟩ := LPi_TowerValues.qm_mul a b ha hb
 have same := qw_injective (value.trans law.symm)
 subst out
 exact ⟨run,canonical⟩

theorem em (a b reply : E) (ha : canonE a) (hb : canonE b)
 (law : EMul a b reply) :
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a b=ok reply ∧ canonE reply := by
 obtain ⟨out,run,canonical,value⟩ := LPi_TowerValues.wide_mul a b ha hb
 have same := ew_injective (value.trans law.symm)
 subst out
 exact ⟨run,canonical⟩

theorem ea (a b reply : E) (ha : canonE a) (hb : canonE b)
 (law : EAdd a b reply) :
 FIo_Native.aspis_core.field.wide_exact.WideExact.add a b=ok reply ∧ canonE reply := by
 obtain ⟨lo,hlo,clo,vlo⟩ := LPi_TowerValues.qm_add a.c0 b.c0 ha.1 hb.1
 obtain ⟨hi,hhi,chi,vhi⟩ := LPi_TowerValues.qm_add a.c1 b.c1 ha.2 hb.2
 have same : (⟨lo,hi⟩ : E)=reply := ew_injective ((Prod.ext vlo vhi).trans law.symm)
 refine ⟨?_,?_⟩
 · rw [←same]
   simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,hlo,hhi,bind_tc_ok]
 · rw [←same]; exact ⟨clo,chi⟩

#print axioms cw_injective
#print axioms qw_injective
#print axioms ew_injective
#print axioms qm
#print axioms em
#print axioms ea
end AspisR1.NIT_FieldInterpretation
