import PV_L2C_ReferenceSub
import PV_L2C_NativeQ
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace PV_L2C_ReferenceQ
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_ReferenceArithmetic PV_L2C_NativeQ
abbrev RawQ := aspis_core.field.QM31

def source (q : Q) : RawQ :=
  ⟨⟨wrap (q 0),wrap (q 1)⟩,⟨wrap (q 2),wrap (q 3)⟩⟩
def model (q : RawQ) : Q := fun i =>
  if i.val=0 then q.c0.a.bv else if i.val=1 then q.c0.b.bv
  else if i.val=2 then q.c1.a.bv else q.c1.b.bv

theorem source_roundtrip (q : RawQ) : source (model q)=q := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  cases a; cases b; cases c; cases d
  rfl
#print axioms source_roundtrip

theorem model_roundtrip (q : Q) : model (source q)=q := by
  funext i
  fin_cases i <;> rfl
#print axioms model_roundtrip

theorem source_zero : source zero=aspis_core.field.QM31.ZERO := by
  unfold aspis_core.field.QM31.ZERO
  rfl
#print axioms source_zero

theorem add_source (x y : Q) :
    aspis_core.field.QM31.add (source x) (source y)=ok (source (addQ x y)) := by
  simp only [aspis_core.field.QM31.add,aspis_core.field.CM31.add,source,
    PV_L2C_ReferenceArithmetic.m31_add,bind_tc_ok] <;> rfl
#print axioms add_source

theorem sub_source (x y : Q) :
    aspis_core.field.QM31.sub (source x) (source y)=ok (source (subQ x y)) := by
  simp only [aspis_core.field.QM31.sub,aspis_core.field.CM31.sub,source,
    PV_L2C_ReferenceSub.m31_sub,bind_tc_ok] <;> rfl
#print axioms sub_source

theorem add_actual (x y : RawQ) :
    aspis_core.field.QM31.add x y=ok (source (addQ (model x) (model y))) := by
  conv_lhs => rw [← source_roundtrip x,← source_roundtrip y]
  exact add_source _ _
#print axioms add_actual

theorem sub_actual (x y : RawQ) :
    aspis_core.field.QM31.sub x y=ok (source (subQ (model x) (model y))) := by
  conv_lhs => rw [← source_roundtrip x,← source_roundtrip y]
  exact sub_source _ _
#print axioms sub_actual
end PV_L2C_ReferenceQ
