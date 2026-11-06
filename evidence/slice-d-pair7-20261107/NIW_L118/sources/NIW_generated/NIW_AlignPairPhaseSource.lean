import NIW_AlignPairPhase
import NIT_ResultCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPairPhaseSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignPairPhase

theorem source (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NIT_PairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 (letI:=FIo_Install.allocation r
  FIo_Native.weights.Weights.pair i.owner.value i.alpha.value.to_slice i.message.value i.kappa)=(run r i).1 ∧
 NIT_ResultCanonical.Canonical (run r i).1 := by
 have certified := certificate r i domain
 generalize execution : run r i=observed at *
 rcases observed with ⟨out,log⟩
 cases p0 : log.powers0 with
 | fail err => simp only [Certificate,p0] at certified
 | div => simp only [Certificate,p0] at certified
 | ok ap0 =>
  cases p1 : log.powers1 with
  | none => simp only [Certificate,p0,p1] at certified
  | some reply =>
   cases reply with
   | fail err => simp only [Certificate,p0,p1] at certified
   | div => simp only [Certificate,p0,p1] at certified
   | ok ap1 =>
    simp only [Certificate,p0,p1] at certified
    rcases certified with ⟨source0,source1,c0,c1,trace⟩
    let c := context i ap0 ap1
    have run := NIT_AllocatorChain.interpreted r c out domain trace
    refine ⟨?_,NIT_ResultCanonical.allocator c r out trace⟩
    letI:=FIo_Install.allocation r
    exact (NIT_PairDomain.source i.owner.value i.alpha.value i.message.value
      (NIT_PairDomain.message_size _ _ _ _ domain) i.kappa).trans
     ((NIT_PairControl.source c source0 source1).trans run)

#print axioms source
end AspisR1.NIW_AlignPairPhaseSource
