import R1Z.PV_OWNC_LinkGrowth
set_option autoImplicit false
namespace R1Z.PV_OWNC_FlatMap
open PV_OWNC_Vector PV_OWN_Link
/-- Each deployed FlatMap closure builds [producer,consumer]; Array::IntoIter
returns those two initialized u16s in order before reading the next Link. -/
def rows : List Link → List UInt16
 | [] => []
 | v::vs => v.producer::v.consumer::rows vs

theorem source_array_order (xs : List Link) :
 rows xs=xs.flatMap (fun v=>[v.producer,v.consumer]) := by
 induction xs with
 | nil => rfl
 | cons v vs ih => simp only [rows,List.flatMap_cons,←ih,List.cons_append,List.nil_append]

theorem count (xs : List Link) : (rows xs).length=2*xs.length := by
 induction xs with
 | nil => rfl
 | cons v vs ih => simp only [rows,List.length_cons,ih];omega

theorem u16_bound (v : UInt16) (i : Nat) (z : UInt8)
 (h:PV_OWN_U16.codec.encode v i=some z) : i<PV_OWN_U16.codec.width := by
 by_cases first:i=0
 · subst i;decide
 · by_cases second:i=1
   · subst i;decide
   · simp only [PV_OWN_U16.codec,PV_OWN_U16.encode,first,second,ite_false] at h

/-- Initialized destination transport for the separate TrustedLen allocation.
Allocation, its ownership token and source destruction remain external stages. -/
theorem initialized (b : Buffer UInt16) (xs : List Link)
 (h:Valid PV_OWN_U16.codec b) (empty:b.length=0)
 (cap:b.capacity=272) (n:xs.length=136) :
 Valid PV_OWN_U16.codec (PV_OWNC_PushFold.append PV_OWN_U16.codec b (rows xs)) ∧
 (PV_OWNC_PushFold.append PV_OWN_U16.codec b (rows xs)).length=272 := by
 have len:(rows xs).length=272 := by rw [count,n]
 refine ⟨PV_OWNC_PushFold.valid _ b _ h (by omega) u16_bound,?_⟩
 rw [PV_OWNC_PushFold.length,empty,len]
#print axioms source_array_order
#print axioms count
#print axioms u16_bound
#print axioms initialized
end R1Z.PV_OWNC_FlatMap
