import R1Z.PV_OWNI_EntryBytes
import R1Z.PV_OWNC_Vector
set_option autoImplicit false
namespace R1Z.PV_OWNI_EmptyVec
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector
/-- Successful RawVec construction after the runtime returns p. Freshness and
alignment are rdea-1; generation and the owner slot are source stores. -/
def token (m : Memory) (p : Nat) : Token := ⟨p,m.generations p+1⟩
def initialized (m : Memory) (p owner capacity : Nat) : Memory :=
 {m with heap:=put m.heap p (some (emptyCell (capacity*24) 8 owner))
         generations:=fun a=>if a=p then m.generations p+1 else m.generations a
         slots:=fun s=>if s=owner then some (token m p) else m.slots s}
def buffer (m : Memory) (p owner capacity : Nat) : Buffer PV_OWNI_EntryBytes.Entry :=
 ⟨initialized m p owner capacity,token m p,owner,emptyCell (capacity*24) 8 owner,
  0,capacity,fun _=>(fun _=>0,fun _=>0)⟩

theorem writable (m : Memory) (p owner capacity : Nat)
 (loans:NoLoans m (token m p)) :
 Writable (initialized m p owner capacity) owner (token m p)
  (emptyCell (capacity*24) 8 owner) := by
 refine ⟨⟨⟨put_same _ _ _,rfl,?_⟩,?_,rfl⟩,loans⟩
 · simp only [initialized,token,ite_true]
 · simp only [initialized,ite_true]

theorem valid (m : Memory) (p owner capacity : Nat)
 (loans:NoLoans m (token m p)) :
 Valid PV_OWNI_EntryBytes.codec (buffer m p owner capacity) := by
 refine ⟨writable m p owner capacity loans,rfl,rfl,Nat.zero_le _,?_⟩
 intro i hi
 change i<0 at hi
 omega

theorem length_zero (m : Memory) (p owner capacity : Nat) :
 (buffer m p owner capacity).length=0 := rfl

theorem byte_extent (m : Memory) (p owner capacity : Nat) :
 (buffer m p owner capacity).cell.size=capacity*24 := rfl
#print axioms writable
#print axioms valid
#print axioms length_zero
#print axioms byte_extent
end R1Z.PV_OWNI_EmptyVec
