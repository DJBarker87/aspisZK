import NMW_Branches
import RSL_TX1_330
set_option autoImplicit false
namespace LIB_RouteCarrier
open Aeneas Aeneas.Std AspisR1
/-- Exact bit-vector carrier change; no byte range assumptions. -/
def byte (b : UInt8) : U8 := ⟨b.toBitVec⟩
def unbyte (b : U8) : UInt8 := UInt8.ofBitVec b.bv
theorem byte_inverse (b : UInt8) : unbyte (byte b) = b := by cases b; rfl
theorem unbyte_inverse (b : U8) : byte (unbyte b) = b := by cases b; rfl
def bytes (b : RSL.Bytes) : List U8 := b.map byte
def unbytes (b : List U8) : RSL.Bytes := b.map unbyte
theorem bytes_inverse (b : RSL.Bytes) : unbytes (bytes b) = b := by
 simp [bytes, unbytes, List.map_map, Function.comp_def, byte_inverse]
theorem unbytes_inverse (b : List U8) : bytes (unbytes b) = b := by
 simp [bytes, unbytes, List.map_map, Function.comp_def, unbyte_inverse]
def args (p : Hiq_DispatchSource.Key) (a : Slice RSL.AccountInfo) (d : Slice U8) :
    RSL.TX2_240.Args :=
  ⟨⟨unbytes p.val, by simpa [unbytes] using p.property⟩, a.val, unbytes d.val⟩
/-- All original descriptors and bytes are passed to each interpreted child. -/
def ops
    (f1 f2 : RSL.TX2_240.Args → RSL.SdkState → RSL.Env →
      RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState))
    (s : RSL.SdkState) (env : RSL.Env) :
    NMW_Symbolic.Ops RSL.AccountInfo
      (RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState)) where
  first := fun p a d => .ok (f1 (args p a d) s env)
  second := fun p a d => .ok (f2 (args p a d) s env)
  init := fun _ _ _ => .ok ⟨.abort, []⟩
  write := fun _ _ _ => .ok ⟨.abort, []⟩
  finalize := fun _ _ _ => .ok ⟨.abort, []⟩
/-- Lifecycle calls are excluded by the process own-input domain and rejected
by entry before process. No claim about those unowned bodies is made. -/
theorem unbytes_eq_iff (x y : List U8) : unbytes x = unbytes y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg bytes h
    simpa only [unbytes_inverse] using h'
  · intro h; rw [h]
theorem stage1_iff (d : Slice U8) :
    RSL.TX2_221.stage1Route (unbytes d.val) = true ↔ Hiq_ReleaseRoute.stage1 d := by
  simp only [RSL.TX2_221.stage1Route, Bool.or_eq_true, beq_iff_eq, Hiq_ReleaseRoute.stage1]
  have h10 : unbytes [3#u8, 10#u8] = [3, 10] := rfl
  have h11 : unbytes [3#u8, 11#u8] = [3, 11] := rfl
  rw [← h10, ← h11, unbytes_eq_iff, unbytes_eq_iff]
theorem asq8_iff (d : Slice U8) :
    (unbytes d.val).take 4 = RSL.REQUEST_MAGIC ↔ Hiq_ReleaseRoute.asq8 d := by
  have ht : (unbytes d.val).take 4 = unbytes (d.val.take 4) := by
    simp only [unbytes, List.map_take]
  have hm : unbytes [65#u8,83#u8,81#u8,56#u8] = RSL.REQUEST_MAGIC := rfl
  rw [ht, ← hm, unbytes_eq_iff]
  rfl
#print axioms unbytes_eq_iff
#print axioms stage1_iff
#print axioms asq8_iff
#print axioms byte_inverse
#print axioms unbyte_inverse
#print axioms bytes_inverse
#print axioms unbytes_inverse
end LIB_RouteCarrier
