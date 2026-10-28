import RPt_JFr_TX2_Scalars
import NDO_JFr_TX2_Tails
import RPt_JFr_TX2_Powers
import NDO_JFr_TX2_DotsBinding
import NDO_JFn_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Partial
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Real-byte input-call non-vacuity. This supplies no native dot-loop,
circle equality, geometry, Merkle, finish or accepted-wrapper result. -/
theorem dot_inputs :
    ∃ g : Array Tx2N_Powers.E 29#usize,
      Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok g ∧
      (∀ j : Fin 29, FIo_WideValues.Canon
        (FIo_Install.toE (g.val[j.val]'(by rw [g.property];exact j.isLt)))) ∧
      (∀ i : Fin 12, ∀ slot : Fin 4, ∀ term : Fin 26,
        ∃ scalar : U32,
          JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array (JFn_Values.position i))
            (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
            (Usize.ofNat term.val (by have:=term.isLt;scalar_tac))=ok scalar ∧
          scalar.val<2147483647) ∧
      (∀ i : Fin 12, ∀ slot : Fin 4, ∀ kind : Fin 3,
        ∃ value, JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFr_TX2_Tails.position i))
          (JFr_TX2_Tails.offset slot kind) (JFr_TX2_Tails.stop slot kind)=ok value) := by
  refine ⟨JFr_TX2_Powers.value,JFr_TX2_Powers.source,JFr_TX2_Powers.canonical,?_,JFr_TX2_Tails.source⟩
  intro i slot term
  exact ⟨_,JFr_TX2_Scalars.source i slot term,JFr_TX2_Scalars.canonical i slot term⟩

/-- Transport to the SAME TX1 saved bytes. The exact three digest realization
equations remain explicit; the computed dot inputs are independent of H. -/
theorem on_saved (saved : alloc.vec.Vec U8)
    (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (seed : Port3_NativeQueryBody.Ops) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok JFr_TX2_Powers.value ∧
    Port3_NativePendingInstall.source true JFo_Prepared.accumulator.weights.deref=ok (.Ok JFo_Pending.value) ∧
    (∀ i : Fin 12,
      (JFr_TX2_DotsBinding.ops seed).op0 4#usize
        (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (JFr_TX2_DotsBinding.ops seed)) (JFo_Opening.value (JFn_Values.position i))=ok (JFn_Values.value i)) ∧
    (∀ i : Fin 12, ∀ slot : Fin 4, ∀ term : Fin 26,
      ∃ scalar : U32,
        JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array (JFn_Values.position i))
          (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
          (Usize.ofNat term.val (by have:=term.isLt;scalar_tac))=ok scalar ∧ scalar.val<2147483647) := by
  refine ⟨JFn_Resume.on_saved saved same H D hash realizes,JFr_TX2_Powers.source,JFo_Pending.source,?_,?_⟩
  · intro i
    exact JFn_Values.source _ i
  · intro i slot term
    exact ⟨_,JFr_TX2_Scalars.source i slot term,JFr_TX2_Scalars.canonical i slot term⟩

#print axioms dot_inputs
#print axioms on_saved
#print on_saved
end AspisR1.JFr_TX2_Partial
end
