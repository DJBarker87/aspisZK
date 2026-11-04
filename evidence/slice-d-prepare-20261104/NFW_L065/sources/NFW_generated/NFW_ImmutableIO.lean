import NFW_BorrowFrame
set_option autoImplicit false
namespace NFW_ImmutableIO
/-- A sequence of local writes, with no assumptions about their values. -/
def writes {A : Type} (memory : Nat→A) : List (Nat×A) → Nat→A
 | [] => memory
 | (address,value)::rest => writes (KMX_CopyMeaning.write memory address value) rest
/-- Every write must be proved disjoint by the native caller. -/
theorem writes_frame {A : Type} (memory : Nat→A) (ws : List (Nat×A))
 (base size offset : Nat) (inside : offset<size)
 (outside : ∀ av∈ws, av.1<base ∨ base+size≤av.1) :
 NFW_BorrowFrame.observe (writes memory ws) base offset=
 NFW_BorrowFrame.observe memory base offset := by
 induction ws generalizing memory with
 | nil => rfl
 | cons av rest ih =>
   change NFW_BorrowFrame.observe (writes (KMX_CopyMeaning.write memory av.1 av.2) rest) base offset=_
   rw [ih _ (by intro x hx; exact outside x (List.mem_cons_of_mem av hx))]
   exact NFW_BorrowFrame.log_frame memory av.1 base size offset av.2 inside
     (outside av (List.mem_cons_self))
def bytes {A : Type} (memory : Nat→A) (view : Nat×Nat) : List A :=
 (List.range view.2).map (fun i => memory (view.1+i))
def parts {A : Type} (memory : Nat→A) (views : List (Nat×Nat)) : List (List A) :=
 views.map (bytes memory)
/-- Shared/overlapping views are allowed. The representation map is explicit. -/
theorem parts_ext {A : Type} (before after : Nat→A) (views : List (Nat×Nat))
 (same : ∀ v∈views, ∀ i<v.2, before (v.1+i)=after (v.1+i)) :
 parts before views=parts after views := by
 apply List.map_congr_left
 intro v hv
 apply List.map_congr_left
 intro i hi
 exact same v hv i (List.mem_range.mp hi)
/-- Exact borrow descriptors and disjoint writes preserve the entire byte list.
This theorem needs a native memory representation instantiation before credit. -/
theorem syscall_parts_frame {A : Type} (memory : Nat→A) (views : List (Nat×Nat))
 (ws : List (Nat×A))
 (outside : ∀ v∈views, ∀ av∈ws, av.1<v.1 ∨ v.1+v.2≤av.1) :
 parts (writes memory ws) views=parts memory views := by
 apply parts_ext
 intro v hv i hi
 exact writes_frame memory ws v.1 v.2 i hi (outside v hv)
/-- A returned reply is preserved independently of the trusted digest value. -/
theorem reply_transport {A B : Type} (value : A) (wrap : A→B) (unwrap : B→A)
 (law : ∀ x, unwrap (wrap x)=x) : unwrap (wrap value)=value := law value
#print axioms writes_frame
#print axioms parts_ext
#print axioms syscall_parts_frame
#print axioms reply_transport
end NFW_ImmutableIO
