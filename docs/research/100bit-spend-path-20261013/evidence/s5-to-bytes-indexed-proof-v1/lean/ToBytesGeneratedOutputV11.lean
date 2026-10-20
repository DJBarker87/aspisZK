import AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions
open Aeneas Aeneas.Std Result Error
namespace AspisR1WideToBytesIndexedCandidate

def limbBytes (w : Std.U32) : List Std.U8 :=
  [(U32.bv w).toLEBytes[0]#uscalar,
   (U32.bv w).toLEBytes[1]#uscalar,
   (U32.bv w).toLEBytes[2]#uscalar,
   (U32.bv w).toLEBytes[3]#uscalar]

theorem limbBytes_length (w : Std.U32) : (limbBytes w).length = 4 := by
  simp [limbBytes]

def expectedList (x : field.wide_exact.WideExact) : List Std.U8 :=
  limbBytes x.c0.c0.a ++ limbBytes x.c0.c0.b ++
  limbBytes x.c0.c1.a ++ limbBytes x.c0.c1.b ++
  limbBytes x.c1.c0.a ++ limbBytes x.c1.c0.b ++
  limbBytes x.c1.c1.a ++ limbBytes x.c1.c1.b

def expectedBytes (x : field.wide_exact.WideExact) : Std.Array Std.U8 32#usize :=
  ⟨expectedList x, by simp [expectedList, limbBytes_length]⟩

private theorem lift_bind_ok {α β : Type} (x : α) (f : α → Result β) :
    (do let y ← Aeneas.Std.lift x; f y) = f x := by
  rfl

theorem indexed_candidate_to_le_bytes (x : field.wide_exact.WideExact) :
    field.wide_exact.WideExact.to_le_bytes x = .ok (expectedBytes x) := by
  unfold field.wide_exact.WideExact.to_le_bytes
  simp only [lift_bind_ok]
  simp [field.wide_exact.WideExact.to_limbs, expectedBytes, expectedList, limbBytes,
    Array.index_usize, Array.update, Array.make, Array.repeat, List.set,
    List.append_assoc, core.num.U32.to_le_bytes]

#print axioms limbBytes_length
#print axioms indexed_candidate_to_le_bytes
end AspisR1WideToBytesIndexedCandidate
