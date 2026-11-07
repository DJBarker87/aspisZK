import NNG_Context094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Guard094
open Aeneas Aeneas.Std Result NMT_tx1

theorem source {H : Type} (c : NNG_Context094.Calls) (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (h : H) (obs : Option (verifier.Phase → Result Unit))
 (bad : (k != compact.SPLIT)=true) :
 NNG_Context094.emitted c D pub publicBytes proof k h obs=.ok (.Err verifier.Error.Parse) := by
 unfold NNG_Context094.emitted verifier.candidate.tx1
 rw [if_pos bad]
#print axioms source

theorem reference (a : RSL.TX1_094.Args LIB_Instances.VL) (bad : (a.k != RSL.SPLIT)=true) :
 RSL.TX1_094.Ref LIB_Instances.VL LIB_Instances.P a=RSL.Spec.pure (.error LIB_Instances.VL.vParse) := by
 unfold RSL.TX1_094.Ref
 rw [bad]
 change RSL.Spec.bind (RSL.Spec.pure (.error LIB_Instances.VL.vParse : Except LIB_Instances.VL.VErr Unit)) _ = _
 rw [RSL.Spec.bind_pure]
#print axioms reference
end AspisR1.NNG_Guard094
