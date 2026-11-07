import NMS_EmittedLinks
import RSL_TX2_241
set_option autoImplicit false
namespace NMS_R2N_RSLScalars
open Aeneas Aeneas.Std
/-- Bit-pattern carrier maps, without modular conversion or canonical-input
restriction. They preserve every unsigned bit pattern in the frozen types. -/
def u8 (x : U8) : UInt8 := UInt8.ofBitVec x.bv
def u32 (x : U32) : UInt32 := UInt32.ofBitVec x.bv
def u64 (x : U64) : UInt64 := UInt64.ofBitVec x.bv
def raw8 (x : UInt8) : U8 := ⟨x.toBitVec⟩
def raw32 (x : UInt32) : U32 := ⟨x.toBitVec⟩
def raw64 (x : UInt64) : U64 := ⟨x.toBitVec⟩

theorem u8_left (x : U8) : raw8 (u8 x) = x := by cases x; rfl
theorem u8_right (x : UInt8) : u8 (raw8 x) = x := by cases x; rfl
theorem u32_left (x : U32) : raw32 (u32 x) = x := by cases x; rfl
theorem u32_right (x : UInt32) : u32 (raw32 x) = x := by cases x; rfl
theorem u64_left (x : U64) : raw64 (u64 x) = x := by cases x; rfl
theorem u64_right (x : UInt64) : u64 (raw64 x) = x := by cases x; rfl

def bytes (x : Slice U8) : RSL.Bytes := x.val.map u8

def b32 (x : Aeneas.Std.Array U8 32#usize) : RSL.B32 :=
 ⟨x.val.map u8,by simpa using x.property⟩

theorem bytes_length (x : Slice U8) : (bytes x).length = x.val.length := List.length_map _

theorem b32_injective {x y : Aeneas.Std.Array U8 32#usize} (h : b32 x = b32 y) : x = y := by
 apply Subtype.ext
 have same := congrArg (fun z : RSL.B32 => z.bytes.map raw8) h
 simp only [b32,List.map_map,Function.comp_def,u8_left] at same
 change x.val.map id = y.val.map id at same
 simpa only [List.map_id] using same

#print axioms u8_left
#print axioms u8_right
#print axioms u32_left
#print axioms u32_right
#print axioms u64_left
#print axioms u64_right
#print axioms bytes_length
#print axioms b32_injective
end NMS_R2N_RSLScalars
