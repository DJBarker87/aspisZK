import R1Z.PV_CBL_ByteCodecValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ShaSerialize
set_option autoImplicit false

def bytes (words : List U32) : List U8 :=
  words.flatMap (fun w => (PV_CBL_ByteCodecValue.store w).val)

def reference : List U32 → Result (List U8)
  | [] => ok []
  | w::tail => do
    let four ← PV_CBL_ShaBytes.sha_store_be4 w
    let rest ← reference tail
    ok (four.val++rest)

theorem source (words : List U32) : reference words=ok (bytes words) := by
  induction words with
  | nil => rfl
  | cons w tail ih =>
    simp only [reference,PV_CBL_ByteCodecValue.store_source,ih,bind_tc_ok,
      bytes,List.flatMap_cons]

theorem length (words : List U32) : (bytes words).length=4*words.length := by
  induction words with
  | nil => rfl
  | cons w tail ih =>
    change ((PV_CBL_ByteCodecValue.store w).val++bytes tail).length=4*(tail.length+1)
    rw [List.length_append,(PV_CBL_ByteCodecValue.store w).property,ih]
    change 4+4*tail.length=4*(tail.length+1)
    omega

def array (state : Array U32 8#usize) : Array U8 32#usize :=
  ⟨bytes state.val,by rw [length,state.property];rfl⟩

theorem total (state : Array U32 8#usize) :
    reference state.val=ok (array state).val := source state.val

#print axioms bytes
#print axioms reference
#print axioms source
#print axioms length
#print axioms array
#print axioms total
end R1Z.PV_DL_ShaSerialize
