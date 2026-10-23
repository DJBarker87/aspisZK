import S2I_ReturnData

/-! Symbolic serialization shape for the emitter's result. These are byte-model
lemmas, not a native encoder port: no successful native validator/encoder call
is assumed or concluded. Rows stay symbolic, avoiding concrete array reduction.
The native iteration and its frame are separate Kani gates. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Serialization

/-- Append each serialized frontier row; native source order is level0..19. -/
def rows (prefix : List U8) (nodes : List (List U8)) : List U8 :=
  nodes.foldl (fun out node => out ++ node) prefix

theorem rows_exact (prefix : List U8) (nodes : List (List U8)) :
    rows prefix nodes = prefix ++ nodes.flatten := by
  induction nodes generalizing prefix with
  | nil => simp only [rows,List.foldl_nil,List.flatten_nil,List.append_nil]
  | cons node nodes ih =>
    simp only [rows,List.foldl_cons]
    rw [← rows, ih]
    simp only [List.flatten_cons,List.append_assoc]

theorem rows_length (prefix : List U8) (nodes : List (List U8))
    (width : ∀ row ∈ nodes, row.length = 32) :
    (rows prefix nodes).length = prefix.length + 32 * nodes.length := by
  induction nodes generalizing prefix with
  | nil => simp only [rows,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons node nodes ih =>
    have hn := width node (by simp)
    have ht : ∀ row ∈ nodes, row.length = 32 := fun row h => width row (by simp [h])
    change (rows (prefix ++ node) nodes).length = _
    rw [ih _ ht,List.length_append,hn,List.length_cons]
    omega

/-- ASJA afterstate bytes consist of48 header/index/root bytes and20 rows32. -/
theorem afterstate_width (prefix : List U8) (nodes : List (List U8))
    (header : prefix.length = 48) (count : nodes.length = 20)
    (width : ∀ row ∈ nodes, row.length = 32) :
    (rows prefix nodes).length = 688 := by
  rw [rows_length prefix nodes width,header,count]

/-- Exact complete ASR8 layout, with supplied canonical digest/afterstate bytes.
Their native success and field semantics must be proved before installation. -/
def resultBytes (kind lane : U8) (master selected nullifier afterstate : List U8) :=
  [65#u8,83#u8,82#u8,56#u8,1#u8,kind,1#u8,lane] ++
    master ++ selected ++ nullifier ++ afterstate

theorem result_width (kind lane : U8) (master selected nullifier afterstate : List U8)
    (hm : master.length = 32) (hs : selected.length = 32)
    (hn : nullifier.length = 32) (ha : afterstate.length = 688) :
    (resultBytes kind lane master selected nullifier afterstate).length = 792 := by
  simp only [resultBytes,List.length_append,List.length_cons,List.length_nil,hm,hs,hn,ha]

theorem emitted_event {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall) (s : S2I.ReturnData.State A E)
    (kind lane : U8) (master selected nullifier afterstate : List U8)
    (hm : master.length = 32) (hs : selected.length = 32)
    (hn : nullifier.length = 32) (ha : afterstate.length = 688) :
    let bytes := resultBytes kind lane master selected nullifier afterstate
    syscall s bytes = ok (S2I.ReturnData.set s bytes) ∧ bytes ≠ [] ∧
    (S2I.ReturnData.set s bytes).accounts = s.accounts ∧
    (S2I.ReturnData.set s bytes).events = s.events ++ [.setReturnData bytes] :=
  S2I.ReturnData.nonempty_event syscall runtime s _
    (result_width kind lane master selected nullifier afterstate hm hs hn ha)

#print axioms rows_exact
#print axioms rows_length
#print axioms afterstate_width
#print axioms result_width
#print axioms emitted_event
end AspisR1.S2K.Serialization
