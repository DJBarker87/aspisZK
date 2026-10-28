import R1Z.PV_RDB1_V183
import R1Z.PV_RDB1_V186
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V181
open PV_RDB1_V183_ReserveWorld

def empty (address : Nat) : Buffer U8 := ⟨address,0,[],by rfl⟩

/-- Actual constructor rejection order: checked layout, zero-sized allocation
bypass, then Global allocate. Buffer fields on an error are an unobserved
empty placeholder, not a Rust return value. Panic/abort is applied afterward. -/
def deployed {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (address n : Nat) (w : World S F) :
    Execution U8 S F :=
  if n>wordMax then ⟨.error .capacityOverflow,empty address,w⟩ else
  if n*shape.width>byteMax then ⟨.error .capacityOverflow,empty address,w⟩ else
  if n=0 then ⟨.ok (),empty address,w⟩ else
  finish step shape (empty address) n w

/-- Owned safe reference: String::new; reserve_exact(n); return the String.
It retains the same allocation request/error/layout effects as with_capacity,
including no allocation or free for n=0. -/
def reference {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (address n : Nat) (w : World S F) :
    Execution U8 S F := native step wordMax byteMax shape (empty address) n w

theorem complete {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (byte_width : shape.width=1)
    (address n : Nat) (w : World S F) :
    deployed step wordMax byteMax shape address n w =
      reference step wordMax byteMax shape address n w := by
  by_cases hz : n=0
  · subst n
    simp only [deployed,reference,native,growExact,empty,List.length_nil,
      Nat.zero_mul,Nat.zero_add,Nat.sub_self,gt_iff_lt,Nat.not_lt_zero,
      ite_false,ite_true]
  · have hn : 0<n := by omega
    simp only [deployed,reference,native,growExact,empty,List.length_nil,
      Nat.zero_add,Nat.sub_self,byte_width,Nat.mul_one,hn,hz,
      show ¬(1=0) by omega,ite_false,ite_true]

/-- Applying the same actual capacity-panic or allocation-abort handler
preserves every Result and allocator/external-state effect of that handler.
No successful allocation is assumed or folded into T. -/
theorem with_handlers {S F R : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (hwidth : shape.width=1)
    (address n : Nat) (w : World S F) (handler : Execution U8 S F → Result R) :
    handler (deployed step wordMax byteMax shape address n w) =
      handler (reference step wordMax byteMax shape address n w) :=
  congrArg handler (complete step wordMax byteMax shape hwidth address n w)

/-- Every returning constructor has zero live bytes, independently of the
requested capacity or allocator address/private state. This is the exact
empty-only String projection consumed by the old bounded value evidence. -/
theorem empty_value {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (hwidth : shape.width=1)
    (address n : Nat) (w : World S F) :
    (deployed step wordMax byteMax shape address n w).buffer.values=[] := by
  rw [complete step wordMax byteMax shape hwidth]
  exact values_preserved step wordMax byteMax shape (empty address) n w

theorem zero_world {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (address : Nat) (w : World S F) :
    deployed step wordMax byteMax shape address 0 w = ⟨.ok (),empty address,w⟩ := by
  simp only [deployed,Nat.zero_mul,gt_iff_lt,Nat.not_lt_zero,ite_false,ite_true]

#print axioms complete
#print axioms with_handlers
#print axioms empty_value
#print axioms zero_world
end R1Z.PV_RDB1_V181
