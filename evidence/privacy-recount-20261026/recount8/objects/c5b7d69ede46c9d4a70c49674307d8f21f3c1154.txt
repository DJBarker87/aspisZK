import R1Z.PV_RDB2D_SparseLayout
namespace R1Z.PV_RDB2D_SparseReserve
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
open PV_RDB2D_SparseShape PV_RDB2D_SparseLayout
set_option autoImplicit false

theorem complete {K S F : Type} (step : Request → S → Option Nat × S)
    (isBoolean : K → Bool) (point : List K) (length : point.length=10)
    (w : World S F) (wordMax byteMax : Nat) (hw : 1024≤wordMax) (hb : 24576≤byteMax) :
    native step wordMax byteMax shape (empty K) (capacity isBoolean point) w =
      finish step shape (empty K) (capacity isBoolean point) w := by
  have hc := capacity_bound isBoolean point length
  have hp := capacity_positive isBoolean point
  have hbyte := byte_bound isBoolean point length
  have nw : ¬capacity isBoolean point>wordMax := by omega
  have nb : ¬capacity isBoolean point*24>byteMax := by omega
  simp only [native,growExact,empty,List.length_nil,Nat.sub_zero,Nat.zero_add,shape,
    hp,show ¬(24=0) by omega,nw,nb,ite_true,ite_false]

/-- Null is the retained allocation-error branch with its complete post-state. -/
theorem null_preserves {K S F : Type} (step : Request → S → Option Nat × S)
    (isBoolean : K → Bool) (point : List K) (w : World S F) (s : S)
    (h : step (request isBoolean point) w.allocator=(none,s)) :
    (finish step shape (empty K) (capacity isBoolean point) w).world.memory=w.memory ∧
    (finish step shape (empty K) (capacity isBoolean point) w).world.live=w.live := by
  have hr : step ⟨8,0,capacity isBoolean point,shape⟩ w.allocator=(none,s) := by
    simpa only [request] using h
  have he : step ⟨(empty K).address,(empty K).capacity,(empty K).values.length+capacity isBoolean point,shape⟩ w.allocator=(none,s) := by
    simpa only [empty,List.length_nil,Nat.zero_add] using hr
  have hh := allocation_error step shape (empty K) (capacity isBoolean point) w s he
  exact ⟨hh.2.2.2.1,hh.2.2.2.2⟩

#print axioms complete
#print axioms null_preserves
end R1Z.PV_RDB2D_SparseReserve
