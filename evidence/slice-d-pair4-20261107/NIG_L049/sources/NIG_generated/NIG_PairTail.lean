import NIG_PairFrames
import NHX_GroupPacket
import NHX_Powers7Edge
set_option autoImplicit false
noncomputable section
namespace NIG_PairTail
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_PairFrames

theorem grouped (w:W) (f:Slice U8) (low:Array NE 16#usize)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (width:f.val.length=2048)
 (hl:canon low) (out:NE)
 (run:FIo_Native.weights.grouped_inactive_pair w f low=ok out):canonE out:=
 NHX_GroupPacket.output w f low s2 width hl out run

theorem put_zero (parts out:Parts) (value:NE) (hp:canon parts) (hv:canonE value)
 (run:Array.update parts 0#usize value=ok out):
 canon out ∧ ∀ i:Nat,i≠0→ out.val[i]?=parts.val[i]?:=by
 exact ⟨NHM_ArrayPreserve.canonical canonE parts out 0#usize value hp hv run,
  fun i different=>NHM_ArrayPreserve.frame parts out 0#usize value run i different⟩

theorem libra (f:Slice U8) (libra:Powers) (parts out:Parts)
 (hl:canon libra) (hp:canon parts)
 (run:FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f parts libra=ok out):canon out:=
 NIG_LibraDomain.source f libra hl parts out hp run

theorem final (kappa:NE) (parts:Parts) (hk:canonE kappa) (hp:canon parts):
 ∃ powers:Parts, FIo_Native.weights.powers 7#usize kappa=ok powers ∧ canon powers ∧
 ∃ out, FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts powers NHI_Scalar.zero=ok out ∧ canonE out:=by
 obtain ⟨powers,run,hpowers⟩:=NHX_Powers7Edge.source kappa hk
 exact ⟨powers,run,hpowers,NHX_FinalTotal.source parts powers hp hpowers⟩
#print axioms grouped
#print axioms put_zero
#print axioms libra
#print axioms final
end NIG_PairTail
