import NHJ_RouteReference
import Hiq_DispatchAdmitted
set_option autoImplicit false
noncomputable section
namespace NHJ_RoutePacket
open Aeneas Aeneas.Std Result
open AspisR1

def byte (values : List U8) (index : Nat) : U8 := values[index]?.getD 0#u8

def header (length : Nat) (a b c d : U8) : Bool := by
  classical
  exact decide ((length=2 ∧ a=3#u8 ∧ (b=10#u8 ∨ b=11#u8)) ∨
    (4≤length ∧ a=65#u8 ∧ b=83#u8 ∧ c=81#u8 ∧ d=56#u8))

def observed (data : Slice U8) : Bool :=
  header data.val.length (byte data.val 0) (byte data.val 1) (byte data.val 2) (byte data.val 3)

private theorem prefix_cases (P : Slice U8 → Prop)
    (zero : ∀ bound, P ⟨[],bound⟩)
    (one : ∀ a bound, P ⟨[a],bound⟩)
    (two : ∀ a b bound, P ⟨[a,b],bound⟩)
    (three : ∀ a b c bound, P ⟨[a,b,c],bound⟩)
    (four : ∀ a b c d tail bound, P ⟨a::b::c::d::tail,bound⟩) : ∀ data, P data := by
  intro ⟨values,bound⟩
  cases values with
  | nil => exact zero bound
  | cons a values => cases values with
    | nil => exact one a bound
    | cons b values => cases values with
      | nil => exact two a b bound
      | cons c values => cases values with
        | nil => exact three a b c bound
        | cons d tail => exact four a b c d tail bound

theorem cohort : ∀ data : Slice U8,
    Hiq_DispatchSource.pool_route.admitted data = ok (observed data) := by
  apply prefix_cases
  all_goals
    intros
    rw [Hiq_DispatchAdmitted.exact]
    simp [observed,header,byte,Hiq_ReleaseRoute.stage1,Hiq_ReleaseRoute.asq8,and_or_left]

private theorem index0 (a : U8) (tail : List U8) (bound) :
    Slice.index_usize ⟨a::tail,bound⟩ 0#usize = ok a := by rfl
private theorem index1 (a b : U8) (tail : List U8) (bound) :
    Slice.index_usize ⟨a::b::tail,bound⟩ 1#usize = ok b := by rfl
private theorem index2 (a b c : U8) (tail : List U8) (bound) :
    Slice.index_usize ⟨a::b::c::tail,bound⟩ 2#usize = ok c := by rfl
private theorem index3 (a b c d : U8) (tail : List U8) (bound) :
    Slice.index_usize ⟨a::b::c::d::tail,bound⟩ 3#usize = ok d := by rfl

theorem extracted : ∀ data : Slice U8,
    NHJ_RouteReference.admitted_ref data = ok (observed data) := by
  apply prefix_cases
  · intro bound
    simp [NHJ_RouteReference.admitted_ref,observed,header,byte,Slice.len]
  · intro a bound
    simp [NHJ_RouteReference.admitted_ref,observed,header,byte,Slice.len]
  · intro a b bound
    by_cases a3 : a=3#u8 <;> by_cases b10 : b=10#u8 <;> by_cases b11 : b=11#u8 <;>
      simp [NHJ_RouteReference.admitted_ref,observed,header,byte,Slice.len,index0,index1,a3,b10,b11]
  · intro a b c bound
    simp [NHJ_RouteReference.admitted_ref,observed,header,byte,Slice.len]
  · intro a b c d tail bound
    have notTwo : Slice.len (⟨a::b::c::d::tail,bound⟩ : Slice U8) ≠ 2#usize := by
      intro same
      have values := congrArg UScalar.val same
      change tail.length+4=2 at values
      omega
    have large : Slice.len (⟨a::b::c::d::tail,bound⟩ : Slice U8) ≥ 4#usize := by
      change tail.length+4 ≥ 4
      omega
    by_cases a65 : a=65#u8 <;> by_cases b83 : b=83#u8 <;>
      by_cases c81 : c=81#u8 <;> by_cases d56 : d=56#u8 <;>
      simp [NHJ_RouteReference.admitted_ref,notTwo,large,index0,index1,index2,index3,
        observed,header,byte,a65,b83,c81,d56]

theorem associate (data : Slice U8) :
    NHJ_RouteReference.admitted_ref data = Hiq_DispatchSource.pool_route.admitted data := by
  rw [extracted,cohort]
#print axioms cohort
#print axioms extracted
#print axioms associate
end NHJ_RoutePacket
