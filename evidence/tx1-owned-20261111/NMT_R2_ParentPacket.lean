import NMT_R2_SelectedPacket
import NMT_345SourceFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ParentPacket
open Aeneas Aeneas.Std NMT_345

def admitted {W : Type} (c : Calls) (s : Parent W) : Result (core.result.Result (NMT_R2_TailPacket.Point W) PE) :=
 if Slice.len s.accounts != 3#usize then NMT_R2_ResultTry.throw .InvalidInstructionData
 else do
  let p ← Slice.index_usize s.accounts 0#usize
  let pub ← Slice.index_usize s.accounts 1#usize
  let ck ← Slice.index_usize s.accounts 2#usize
  NMT_R2_SelectedPacket.selected c ⟨s,p,pub,ck⟩

theorem admitted_source {W : Type} (c : Calls) (s : Parent W) :
 NMT_R2_ResultTry.bind (admitted c s) (NMT_R2_TailPacket.finish c) = admittedFold c s := by
 simp only [admitted,Bind.bind,NMT_R2_ResultTry.choose,NMT_R2_ResultTry.throw_left,
  NMT_R2_ResultTry.outer,NMT_R2_SelectedPacket.source]
 rfl

def packet {W : Type} (c : Calls) (s : Parent W) : Result (core.result.Result (NMT_R2_TailPacket.Point W) PE) := do
 let route10 ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,10#u8])
 if route10 then admitted c s else do
  let route11 ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8])
  if route11 then admitted c s else NMT_R2_ResultTry.throw .InvalidInstructionData

theorem route_source {W : Type} (c : Calls) (s : Parent W) :
 NMT_R2_ResultTry.bind (packet c s) (NMT_R2_TailPacket.finish c) = sourceFold c s := by
 simp only [packet,Bind.bind,NMT_R2_ResultTry.outer,NMT_R2_ResultTry.choose,
  NMT_R2_ResultTry.throw_left,admitted_source]
 rfl

/-- Complete E003 VALUE/CONTROL association at its only eventful child. Every
call-point field retains its source parent. Observable producer association is
separate; this theorem does not promote a row by output equality. -/
theorem emitted_source {W : Type} (c : Calls) (s : Parent W) :
 emitted c s = NMT_R2_ResultTry.bind (packet c s) (NMT_R2_TailPacket.finish c) := by
 rw [NMT_345.source_fold]
 exact (route_source c s).symm
#print axioms admitted_source
#print axioms route_source
#print axioms emitted_source
end NMT_R2_ParentPacket
end
