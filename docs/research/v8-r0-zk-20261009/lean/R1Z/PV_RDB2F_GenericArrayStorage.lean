import R1Z.PV_RDB2F_NativeShaFrame
namespace R1Z.PV_RDB2F_GenericArrayStorage
set_option autoImplicit false
/-- The deployed ArrayLength recursion: UTerm, UInt<N,B0>, UInt<N,B1>.
repr(C) and repr(transparent) preservation are the retained compiler boundary. -/
inductive Storage (T : Type) : Nat → Type where
  | empty : Storage T 0
  | even {n : Nat} : Storage T n → Storage T n → Storage T (2*n)
  | odd {n : Nat} : Storage T n → Storage T n → T → Storage T (2*n+1)

def flatten {T : Type} {n : Nat} : Storage T n → List T
  | .empty => []
  | .even a b => flatten a++flatten b
  | .odd a b value => flatten a++flatten b++[value]

theorem storage_length {T : Type} {n : Nat} (native : Storage T n) :
    (flatten native).length=n := by
  induction native with
  | empty => rfl
  | even a b ha hb => simp only [flatten,List.length_append,ha,hb];omega
  | odd a b value ha hb => simp only [flatten,List.length_append,List.length_singleton,ha,hb];omega

/-- Deref/DerefMut see the same complete initialized byte sequence. -/
def bytes {T : Type} {n : Nat} (native : Storage T n) : {xs : List T // xs.length=n} :=
  ⟨flatten native,storage_length native⟩

theorem deref_same_bytes {T : Type} {n : Nat} (native : Storage T n) :
    (bytes native).val=flatten native := rfl

theorem sha_buffer64 (native : Storage Aeneas.Std.U8 64) : (bytes native).val.length=64 :=
  (bytes native).property

theorem sha_output32 (native : Storage Aeneas.Std.U8 32) : (bytes native).val.length=32 :=
  (bytes native).property

#print axioms storage_length
#print axioms deref_same_bytes
#print axioms sha_buffer64
#print axioms sha_output32
end R1Z.PV_RDB2F_GenericArrayStorage
