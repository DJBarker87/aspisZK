import R1Z.PV_DL_CtFinal
import R1Z.PV_DL_StorageBuild
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_DL_CtCarrier
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
set_option autoImplicit false
abbrev Full (N : Type) := GenericArray U8 N (Storage U8 5)
abbrev Output (N : Type) (s : PV_DL_ArrayShape.Shape) := GenericArray U8 N (PV_DL_ArrayShape.Carrier U8 s)

def initial (N : Type) : Full N := ⟨PV_DL_StorageBuild.build 5 (fun _ => 0#u8)⟩

theorem initial_byte (N : Type) (i : Fin 32) :
    (flatten 5 (initial N).data)[i.val]?=some 0#u8 := by
  simp only [initial,PV_DL_StorageBuild.flatten_build,List.getElem?_ofFn]
  exact if_pos (show i.val<2^5 from i.isLt)

def adapted {T A N : Type} (finish : T → Buffer A → Full N → Result (T × Buffer A × Full N))
    (state : T) (buffer : Buffer A) (_ : List U8) : Result (T × Buffer A × List U8) := do
  let (state,buffer,full) ← finish state buffer (initial N)
  ok (state,buffer,flatten 5 full.data)

def callback {T A N OutN : Type}
    (finish : T → Buffer A → Full N → Result (T × Buffer A × Full N))
    (side : Result PV_DL_CtFinal.Side) (s : PV_DL_ArrayShape.Shape)
    (self : CtWrapper T) (buffer : Buffer A) (_ : Output OutN s) :
    Result (CtWrapper T × Buffer A × Output OutN s) := do
  let (state,buffer,full) ← finish self.inner buffer (initial N)
  let direction ← side
  if PV_DL_ArrayShape.size s≤32 then
    let bytes := PV_DL_Truncation.value direction (PV_DL_ArrayShape.size s) (flatten 5 full.data)
    ok (⟨state,()⟩,buffer,⟨PV_DL_ArrayShape.build s (fun i => bytes[i]!)⟩)
  else fail .panic

def value {T A N OutN : Type}
    (finish : T → Buffer A → Full N → Result (T × Buffer A × Full N))
    (side : Result PV_DL_CtFinal.Side) (s : PV_DL_ArrayShape.Shape)
    (self : CtWrapper T) (buffer : Buffer A) :
    Result (CtWrapper T × Buffer A × Output OutN s) := do
  let (state,buffer,bytes) ← PV_DL_CtFinal.reference
    (ok (flatten 5 (initial N).data)) (adapted finish) side (PV_DL_ArrayShape.size s) self.inner buffer
  ok (⟨state,()⟩,buffer,⟨PV_DL_ArrayShape.build s (fun i => bytes[i]!)⟩)

theorem complete {T A N OutN : Type}
    (finish : T → Buffer A → Full N → Result (T × Buffer A × Full N))
    (side : Result PV_DL_CtFinal.Side) (s : PV_DL_ArrayShape.Shape)
    (self : CtWrapper T) (buffer : Buffer A) (out : Output OutN s) :
    callback finish side s self buffer out=value finish side s self buffer := by
  unfold callback value PV_DL_CtFinal.reference adapted
  simp only [bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result hr
  rcases result with ⟨changed,restored,full⟩
  simp only [Aeneas.Std.uncurry,bind_tc_ok]
  have hl : (flatten 5 full.data).length=32 := PV_CBL_GenericArrayPower.length 5 full.data
  rw [hl]
  cases side with
  | fail e => rfl
  | div => rfl
  | ok direction =>
    by_cases hs : PV_DL_ArrayShape.size s≤32
    · simp only [bind_tc_ok,if_pos hs,Aeneas.Std.uncurry]
    · simp only [bind_tc_ok,if_neg hs,bind_tc_fail]

theorem decoded {OutN : Type} (s : PV_DL_ArrayShape.Shape) (bytes : List U8)
    (h : bytes.length=PV_DL_ArrayShape.size s) :
    PV_DL_ArrayShape.flatten s
      (show Output OutN s from ⟨PV_DL_ArrayShape.build s (fun i => bytes[i]!)⟩).data=bytes :=
  PV_DL_ArrayShape.reconstruct s bytes h

#print axioms initial
#print axioms initial_byte
#print axioms adapted
#print axioms callback
#print axioms value
#print axioms complete
#print axioms decoded
end R1Z.PV_DL_CtCarrier
