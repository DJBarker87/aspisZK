import S6SliceFrameContentsV1
set_option autoImplicit false
namespace AspisS6SliceFrame

/-- A point write immediately after an initialized lead preserves the suffix. -/
theorem set_append_point {T : Type} (lead : List T) (remaining : Nat)
    (zero value : T) :
    (lead++List.replicate (remaining+1) zero).set lead.length value =
      (lead++[value])++List.replicate remaining zero := by
  induction lead with
  | nil => simp [List.set,List.replicate_succ]
  | cons x xs ih => simpa [List.set] using congrArg (List.cons x) ih

/-- The payment common writer changes bytes0..6 and preserves initialized byte7.
This is the exact source behavior, rather than an invented byte7 write. -/
theorem payment_header_writes {T : Type} (magic : List T) (hmagic : magic.length=4)
    (zero version kind encoding : T) :
    ((((List.replicate 216 zero).setSlice! 0 magic).set 4 version).set 5 kind).set 6 encoding =
      (magic++[version,kind,encoding,zero])++List.replicate 208 zero := by
  have h0 := setSlice_append_chunk [] magic 216 zero (by rw [hmagic]; decide)
  simp only [List.length_nil,List.nil_append,hmagic,Nat.reduceSub] at h0
  rw [h0]
  have h1 := set_append_point magic 211 zero version
  simp only [hmagic,Nat.reduceAdd] at h1
  rw [h1]
  have h2 := set_append_point (magic++[version]) 210 zero kind
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h2
  rw [h2]
  have h3 := set_append_point ((magic++[version])++[kind]) 209 zero encoding
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h3
  rw [h3]
  rw [show (209 : Nat)=208+1 from rfl,List.replicate_succ]
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.singleton_append]

#print axioms set_append_point
#print axioms payment_header_writes
end AspisS6SliceFrame
