import R1Z.PV_RDB2D_CollectorTrace
namespace R1Z.PV_RDB2D_AmortizedReserve
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
open PV_RDB2D_CollectorShape PV_RDB2D_CollectorTrace
set_option autoImplicit false

def native {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (world : World S F) : Execution T S F :=
  if additional > b.capacity-b.values.length then
    let cap := amortized shape.width b.capacity b.values.length additional
    growExact step wordMax byteMax shape b (cap-b.values.length) world
  else ⟨.ok (),b,world⟩

def reference {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (world : World S F) : Execution T S F :=
  if additional > b.capacity-b.values.length then
    let cap := amortized shape.width b.capacity b.values.length additional
    if shape.width=0 ∨ b.values.length+(cap-b.values.length)>wordMax ∨
        (b.values.length+(cap-b.values.length))*shape.width>byteMax then
      ⟨.error .capacityOverflow,b,world⟩
    else finish step shape b (cap-b.values.length) world
  else ⟨.ok (),b,world⟩

theorem complete {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (world : World S F) :
    native step wordMax byteMax shape b additional world =
      reference step wordMax byteMax shape b additional world := by
  unfold native reference growExact
  split
  · dsimp only
    by_cases z : shape.width=0 <;>
      by_cases a : b.values.length + (amortized shape.width b.capacity b.values.length additional-b.values.length)>wordMax <;>
      by_cases l : (b.values.length + (amortized shape.width b.capacity b.values.length additional-b.values.length))*shape.width>byteMax <;>
      simp only [z,a,l,or_true,true_or,or_false,false_or,ite_true,ite_false]
  · rfl

theorem selected {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=8) (b : Buffer T)
    (len : b.values.length=64) (cap : b.capacity=127) (world : World S F)
    (wordMax byteMax : Nat) (hw : 254≤wordMax) (hb : 2032≤byteMax) :
    native step wordMax byteMax shape b 72 world = finish step shape b 190 world := by
  unfold native growExact
  simp only [len,cap,width]
  have growth : (72:Nat)>127-64 := by omega
  have nw : ¬64+190>wordMax := by omega
  have nb : ¬(64+190)*8>byteMax := by omega
  simp only [growth,ite_true,show amortized 8 127 64 72=254 by rfl,
    show (254:Nat)-64=190 by rfl,show ¬(8=0) by omega,nw,nb,ite_false]

theorem request_capacity {T : Type} (b : Buffer T) (len : b.values.length=64) :
    b.values.length+190=254 := by omega

theorem constructor_request {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=8) (w : World S F)
    (wordMax byteMax : Nat) (hw : 127≤wordMax) (hb : 1016≤byteMax) :
    growExact step wordMax byteMax shape (empty T) 127 w =
      finish step shape (empty T) 127 w := by
  have nw : ¬(127:Nat)>wordMax := by omega
  have nb : ¬(1016:Nat)>byteMax := by omega
  simp only [growExact,empty,List.length_nil,Nat.zero_add,width,
    show ¬(8=0) by omega,show (127:Nat)*8=1016 by rfl,nw,nb,ite_false]

theorem rows_request {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=2) (w : World S F)
    (wordMax byteMax : Nat) (hw : 272≤wordMax) (hb : 544≤byteMax) :
    growExact step wordMax byteMax shape (empty Nat) 272 w =
      finish step shape (empty Nat) 272 w := by
  have nw : ¬(272:Nat)>wordMax := by omega
  have nb : ¬(544:Nat)>byteMax := by omega
  simp only [growExact,empty,List.length_nil,Nat.zero_add,width,
    show ¬(2=0) by omega,show (272:Nat)*2=544 by rfl,nw,nb,ite_false]

#print axioms complete
#print axioms selected
#print axioms request_capacity
#print axioms constructor_request
#print axioms rows_request
end R1Z.PV_RDB2D_AmortizedReserve
