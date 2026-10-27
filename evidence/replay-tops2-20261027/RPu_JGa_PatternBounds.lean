import RPu_JFy_Steps
import RPu_FIq_Native13
set_option autoImplicit false
namespace AspisR1.JGa_PatternBounds
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def Good (p : CompiledPoolV1PairForestPattern) : Prop :=
  (∀ x∈p.columns.val,x.val<16) ∧ (∀ x∈p.offsets.val,x.val<2147483647)

theorem p00 : Good pattern00 := by
  simp [Good,pattern00,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p00

theorem p01 : Good pattern01 := by
  simp [Good,pattern01,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p01

theorem p02 : Good pattern02 := by
  simp [Good,pattern02,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p02

theorem p03 : Good pattern03 := by
  simp [Good,pattern03,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p03

theorem p04 : Good pattern04 := by
  simp [Good,pattern04,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p04

theorem p05 : Good pattern05 := by
  simp [Good,pattern05,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p05

theorem p06 : Good pattern06 := by
  simp [Good,pattern06,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p06

theorem p07 : Good pattern07 := by
  simp [Good,pattern07,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p07

theorem p08 : Good pattern08 := by
  simp [Good,pattern08,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p08

theorem p09 : Good pattern09 := by
  simp [Good,pattern09,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p09

theorem p10 : Good pattern10 := by
  simp [Good,pattern10,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p10

theorem p11 : Good pattern11 := by
  simp [Good,pattern11,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p11

theorem p12 : Good pattern12 := by
  simp [Good,pattern12,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p12

theorem p13 : Good pattern13 := by
  simp [Good,pattern13,Array.make,Array.repeat]
  <;> scalar_tac
#print axioms p13

theorem all : ∀ p∈constants.COPY_PATTERNS.val,Good p := by
  intro p hp
  simp only [constants.COPY_PATTERNS,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact p00 | exact p01 | exact p02 | exact p03 | exact p04 | exact p05 | exact p06 | exact p07 | exact p08 | exact p09 | exact p10 | exact p11 | exact p12 | exact p13
#print axioms all
end AspisR1.JGa_PatternBounds
