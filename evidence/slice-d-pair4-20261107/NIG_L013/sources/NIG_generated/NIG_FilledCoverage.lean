import NHX_FilledZero
set_option autoImplicit false
namespace NIG_FilledCoverage
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel

/-- Symbolic coverage of the four-length native cuts and the two disjoint
32-cell observation windows. No concrete large finite set is evaluated. -/
theorem covered (p k:Nat) (hp:p<64) (hk:k≤p) :
 ∃ b w, b%4=0 ∧ b<64 ∧ b≤p ∧ p<b+4 ∧
 (w=0 ∨ w=32) ∧ w≤k ∧ k<w+32 ∧ w≤b+3 := by
 refine ⟨4*(p/4),(if k<32 then 0 else 32),?_,?_,?_,?_,?_,?_,?_,?_⟩
 · omega
 · omega
 · omega
 · omega
 · split <;> simp
 · split <;> omega
 · split <;> omega
 · split <;> omega

/-- The SAME initialized zero prefix is extended by one zero. The caller
invariant leaves all other spare storage unspecified. -/
theorem prefix (p:Nat) :
 NHM_Filled64.cells NHX_FilledZero.zeroQ (p+1)=
 NHX_FilledPacket.window (NHM_Filled64.cells NHX_FilledZero.zeroQ p) NHX_FilledZero.zeroQ := by
 rw [NHM_Filled64.initialization,NHM_Filled64.initialization]
 exact NHM_FilledFrame.grow p NHX_FilledZero.zeroQ

/-- Full allocator reply is preserved by the inherited emitted/cohort law;
there is no reserve-success or allocation-availability precondition. -/
theorem source (reservation:Reservation) :
 letI:=FIo_Install.allocation reservation
 FIo_FieldBridge.map NHM_Filled64.reply
  (FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHX_FilledZero.zeroQ)=
 NHI_FilledRef.filled_ref 64#usize (NHI_WordEncoding.words NHX_FilledZero.zeroQ):=
 NHX_FilledZero.source reservation
#print axioms covered
#print axioms prefix
#print axioms source
end NIG_FilledCoverage
