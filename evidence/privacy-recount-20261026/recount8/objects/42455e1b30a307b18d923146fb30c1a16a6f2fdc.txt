import R1Z.ProverRwSuccessInverseInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessArithmeticTotal
open Aeneas Aeneas.Std Result
open AspisR1ProducerRelease47

def Total {A : Type} (r : Result A) : Prop := ∃ a,r=.ok a

theorem ok_total {A : Type} (a : A) : Total (.ok a) := ⟨a,rfl⟩
theorem bind_total {A B : Type} {r : Result A} {f : A → Result B}
    (hr : Total r) (hf : ∀ a,Total (f a)) : Total (r >>= f) := by
  obtain ⟨a,ha⟩ := hr
  rw [ha]
  exact hf a

theorem mapped_total {A B : Type} (f : A → B) (r : Result A) (hr : Total r) :
    Total (ProverRwDictionaryTower.mapResult f r) := by
  obtain ⟨a,ha⟩ := hr
  exact ⟨f a,by rw [ha]; rfl⟩

theorem m_add (a b : U32) : Total (field.M31.add a b) := by
  simp only [field.M31.add,lift,bind_tc_ok]
  split <;> exact ok_total _
theorem m_sub (a b : U32) : Total (field.M31.sub a b) := by
  simp only [field.M31.sub,lift,bind_tc_ok]
  split <;> exact ok_total _
theorem m_mul (a b : U32) : Total (field.M31.mul a b) :=
  ProverRwSuccessPowerTotal.mul_total a b
theorem m_reduce (a : U64) : Total (field.M31.reduce_u64 a) := by
  simp only [field.M31.reduce_u64,field.reduce_u64,lift,bind_tc_ok]
  split <;> exact ok_total _
theorem m_neg (a : U32) : Total (field.M31.neg a) := by
  simp only [field.M31.neg,lift,bind_tc_ok]
  split <;> exact ok_total _

theorem c_mul (a b : field.CM31) : Total (field.CM31.mul a b) := by
  unfold field.CM31.mul
  apply bind_total (m_mul _ _);intro _
  apply bind_total (m_mul _ _);intro _
  simp only [lift,bind_tc_ok]
  apply bind_total (m_reduce _);intro _
  apply bind_total (m_sub _ _);intro _
  apply bind_total (m_sub _ _);intro _
  apply bind_total (m_sub _ _);intro _
  exact ok_total _
theorem c_sub (a b : field.CM31) : Total (field.CM31.sub a b) := by
  unfold field.CM31.sub
  apply bind_total (m_sub _ _);intro _
  apply bind_total (m_sub _ _);intro _
  exact ok_total _
theorem c_neg (a : field.CM31) : Total (field.CM31.neg a) := by
  unfold field.CM31.neg
  apply bind_total (m_neg _);intro _
  apply bind_total (m_neg _);intro _
  exact ok_total _
#print axioms ok_total
#print axioms bind_total
#print axioms mapped_total
#print axioms m_add
#print axioms m_sub
#print axioms m_mul
#print axioms m_reduce
#print axioms m_neg
#print axioms c_mul
#print axioms c_sub
#print axioms c_neg
end R1Z.ProverRwSuccessArithmeticTotal
