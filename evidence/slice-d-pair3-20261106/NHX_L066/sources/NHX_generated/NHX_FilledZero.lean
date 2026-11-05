import NHX_FilledPacket
set_option autoImplicit false
namespace NHX_FilledZero
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel
abbrev zeroQ:=FIo_Native.aspis_core.field.QM31.ZERO

theorem zero_canonical:canonQ zeroQ:=by
 unfold zeroQ FIo_Native.aspis_core.field.QM31.ZERO
 simp only [canonQ,canonC,LPi_CMProduct.Canon]
 decide

/-- The actual S2 pair caller fills64 QM31 cells with ZERO. Only the initialized
prefix is zero; native spare storage is left arbitrary. -/
theorem prefix_domain (n:Nat) : ∀ q∈NHM_Filled64.cells zeroQ n,q=zeroQ ∧ canonQ q:=by
 intro q hq
 rw [NHM_Filled64.initialization] at hq
 have same:= (List.mem_replicate.mp hq).2
 exact ⟨same,by rw [same];exact zero_canonical⟩

theorem preserves (before:List NQ) (h:∀ q∈before,q=zeroQ) :
 ∀ q∈NHX_FilledPacket.window before zeroQ,q=zeroQ:=by
 intro q hq
 simp only [NHX_FilledPacket.window,List.mem_append,List.mem_singleton] at hq
 rcases hq with hb|hz
 · exact h q hb
 · exact hz

/-- Full allocator Error/Ok law, specialized to the actual SAME zero64 caller.
No reservation success or allocator availability is assumed. -/
theorem source (reservation:Reservation) :
 letI:=FIo_Install.allocation reservation
 FIo_FieldBridge.map NHM_Filled64.reply
  (FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize zeroQ)=NHI_FilledRef.filled_ref 64#usize (NHI_WordEncoding.words zeroQ):=
 NHX_FilledPacket.source reservation zeroQ

#print axioms zero_canonical
#print axioms prefix_domain
#print axioms preserves
#print axioms source
end NHX_FilledZero
