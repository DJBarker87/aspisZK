import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_WordIdentity
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem cm (x y : NC) (h : cw x=cw y) : x=y := by
  rcases x with ⟨a,b⟩;rcases y with ⟨c,d⟩
  have ha : a.val=c.val := congrArg Prod.fst h
  have hb : b.val=d.val := congrArg Prod.snd h
  have := UScalar.eq_of_val_eq ha
  have := UScalar.eq_of_val_eq hb
  simp_all

theorem qm (x y : NQ) (h : qw x=qw y) : x=y := by
  rcases x with ⟨a,b⟩;rcases y with ⟨c,d⟩
  have ha:=cm a c (congrArg Prod.fst h)
  have hb:=cm b d (congrArg Prod.snd h)
  simp_all

theorem wide (x y : NE) (h : ew x=ew y) : x=y := by
  rcases x with ⟨a,b⟩;rcases y with ⟨c,d⟩
  have ha:=qm a c (congrArg Prod.fst h)
  have hb:=qm b d (congrArg Prod.snd h)
  simp_all

/-- Unlike an assumed successful emitted call, this constructs that call
from the exact natural-value log law and canonical INPUT domains. -/
theorem qm_call (x y reply : NQ) (hx : canonQ x) (hy : canonQ y)
    (value : qw reply=mulQ (qw x) (qw y)) :
    FIo_Native.aspis_core.field.QM31.mul x y=ok reply := by
  obtain ⟨z,run,_,hz⟩ := LPi_TowerValues.qm_mul x y hx hy
  have same:=qm z reply (hz.trans value.symm)
  simpa only [same] using run

theorem wide_call (x y reply : NE) (hx : canonE x) (hy : canonE y)
    (value : ew reply=mulE (ew x) (ew y)) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok reply := by
  obtain ⟨z,run,_,hz⟩ := LPi_TowerValues.wide_mul x y hx hy
  have same:=wide z reply (hz.trans value.symm)
  simpa only [same] using run

#print axioms cm
#print axioms qm
#print axioms wide
#print axioms qm_call
#print axioms wide_call
end NCJ_WordIdentity
