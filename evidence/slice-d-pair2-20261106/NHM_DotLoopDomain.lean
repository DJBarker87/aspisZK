import NHM_HighDot
import NHM_PartialDot
import NHM_ByteProducts
import NHM_LoopDomain
import NHM_DotInitial
set_option autoImplicit false
namespace NHM_DotLoopDomain
open Aeneas Aeneas.Std Result ControlFlow
abbrev State := NHI_HighDotLoop.State

structure Inv (n : Nat) (s : State) : Prop where
 count : s.2.count.val=s.1.start.val
 last : s.1.end.val=n
 bounded : s.1.start.val≤n

def initial (n : Usize) : State := ({start:=0#usize,«end»:=n},NHM_DotInitial.zero)

theorem initial_domain (n : Usize) : Inv n.val (initial n) := ⟨rfl,rfl,by simp [initial]⟩

theorem high_step (p : Array NHM_DotPacket.NE 4#usize) (q : Array NHM_DotPacket.NQ 4#usize)
 (s t : State) (h : Inv 4 s) (run : NHM_HighDot.body p q s=ok (.cont t)) : Inv 4 t := by
 obtain ⟨count,last,bound⟩ := NHM_HighDot.invariant p q s t h.count h.last run
 exact ⟨count,last,by omega⟩

theorem partial_step (f : Slice U8) (q : Array NHM_DotPacket.NQ 16#usize) (offset : Usize)
 (s t : State) (h : Inv 16 s) (run : NHM_PartialDot.body f q offset s=ok (.cont t)) : Inv 16 t := by
 obtain ⟨count,last,bound⟩ := NHM_PartialDot.invariant f q offset s t h.count h.last run
 exact ⟨count,last,by omega⟩

theorem byte_step (f : Slice U8) (q : Slice NHM_DotPacket.NQ) (n : Nat)
 (s t : State) (h : Inv n s) (run : NHM_ByteProducts.body f q s=ok (.cont t)) : Inv n t := by
 obtain ⟨count,last,bound⟩ := NHM_ByteProducts.invariant f q s t h.count n h.last run
 exact ⟨count,last,by omega⟩

theorem high_all (p : Array NHM_DotPacket.NE 4#usize) (q : Array NHM_DotPacket.NQ 4#usize) :
 NHM_LoopDomain.all (NHM_HighDot.body p q) (Inv 4) 5 (initial 4#usize) :=
 NHM_LoopDomain.invariant _ _ (high_step p q) _ _ (initial_domain _)

theorem partial_all (f : Slice U8) (q : Array NHM_DotPacket.NQ 16#usize) (offset : Usize) :
 NHM_LoopDomain.all (NHM_PartialDot.body f q offset) (Inv 16) 17 (initial 16#usize) :=
 NHM_LoopDomain.invariant _ _ (partial_step f q offset) _ _ (initial_domain _)

theorem byte_all (f : Slice U8) (q : Slice NHM_DotPacket.NQ) :
 NHM_LoopDomain.all (NHM_ByteProducts.body f q) (Inv 64) 65 (initial 64#usize) :=
 NHM_LoopDomain.invariant _ _ (byte_step f q 64) _ _ (initial_domain _)

#print axioms initial_domain
#print axioms high_step
#print axioms partial_step
#print axioms byte_step
#print axioms high_all
#print axioms partial_all
#print axioms byte_all
end NHM_DotLoopDomain
