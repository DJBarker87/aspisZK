import EbyKFinishTotal
import CurrentWideField
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKFinish.Proof
open AspisV8R17.RawReducer

def toCurrentCM (x : field.CM31) : AspisR1CurrentWide.field.CM31 := ⟨x.a,x.b⟩
def toCurrentQM (x : field.QM31) : AspisR1CurrentWide.field.QM31 := ⟨toCurrentCM x.c0,toCurrentCM x.c1⟩
def toCurrentWide (x : field.wide_exact.WideExact) : AspisR1CurrentWide.field.wide_exact.WideExact :=
  ⟨toCurrentQM x.c0,toCurrentQM x.c1⟩

theorem finish_output_current_canonical (self : EbyKDot) (out : field.wide_exact.WideExact)
    (h : EbyKDot.finish self = .ok out) :
    AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide out) ∧
      finishLimbs out=(self.c0.sums.val++self.c1.sums.val).map word := by
  obtain ⟨result,hr,hlimbs,hcanon⟩ := eby_finish_total self
  have he : result=out := Result.ok.inj (hr.symm.trans h)
  subst result
  have h0 := hcanon out.c0.c0.a (by simp [finishLimbs])
  have h1 := hcanon out.c0.c0.b (by simp [finishLimbs])
  have h2 := hcanon out.c0.c1.a (by simp [finishLimbs])
  have h3 := hcanon out.c0.c1.b (by simp [finishLimbs])
  have h4 := hcanon out.c1.c0.a (by simp [finishLimbs])
  have h5 := hcanon out.c1.c0.b (by simp [finishLimbs])
  have h6 := hcanon out.c1.c1.a (by simp [finishLimbs])
  have h7 := hcanon out.c1.c1.b (by simp [finishLimbs])
  exact ⟨⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩,hlimbs⟩

#print axioms finish_output_current_canonical
end AspisR1EbyKFinish.Proof
