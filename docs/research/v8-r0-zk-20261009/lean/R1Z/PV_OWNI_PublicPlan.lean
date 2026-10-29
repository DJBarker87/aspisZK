import R1Z.PV_RDB2D_SparsePublic
import R1Z.PV_OWNI_RawConsumer
set_option autoImplicit false
namespace R1Z.PV_OWNI_PublicPlan
open PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape
/-- The resource projection retains public failure position and stops at the
first wrong-length or null allocation. Successful POD drop follows each call. -/
def plan {K : Type} (isBoolean : K → Bool) (point : List K) :
 List Nat → List Bool → List Action
 | [],_ => []
 | len::rest,failures =>
  if len≠1024 then [] else
  let bytes:=24*capacity isBoolean point
  if failures.headD false then [.allocate bytes 8,.abort bytes 8] else
  [.allocate bytes 8,.deallocate bytes 8]++plan isBoolean point rest failures.tail

theorem same_public {K : Type} (isBoolean : K → Bool) (left right : List K)
 (hl:left=right) (lengths other : List Nat) (hn:lengths=other) (failures : List Bool) :
 plan isBoolean left lengths failures=plan isBoolean right other failures := by
 rw [hl,hn]

theorem one_success {K : Type} (isBoolean : K → Bool) (point : List K) :
 plan isBoolean point [1024] [false]=
 [.allocate (24*capacity isBoolean point) 8,.deallocate (24*capacity isBoolean point) 8] := rfl

theorem one_null {K : Type} (isBoolean : K → Bool) (point : List K) :
 plan isBoolean point [1024] [true]=
 [.allocate (24*capacity isBoolean point) 8,.abort (24*capacity isBoolean point) 8] := rfl

theorem wrong_length {K : Type} (isBoolean : K → Bool) (point : List K)
 (len : Nat) (rest : List Nat) (failures : List Bool) (h:len≠1024) :
 plan isBoolean point (len::rest) failures=[] := by rw [plan,if_pos h]

#print axioms same_public
#print axioms one_success
#print axioms one_null
#print axioms wrong_length
end R1Z.PV_OWNI_PublicPlan
