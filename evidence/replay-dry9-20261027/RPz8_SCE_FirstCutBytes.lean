import RPz8_SCE_SnapshotRead
import RPz8_SCE_SuffixShape
import S2W_NativeConsolidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FirstCutBytes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_NativeConsolidation
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical SCE_Experiment

/-- On the canonical full SourceCuts witness, the actual selected TX1 proof
and physical public are precisely the shared adversary's submitted bytes. -/
theorem submitted_cut {A : Type} (i : GExq_AccountExperiment.FirstInputs A)
    (ops : AdapterRw.Ops) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops i.entry.first accounts2 saved f s) :
    (submitted i).publicBytes = bytesOf f.pub.val ∧
      (submitted i).stored = bytesOf f.proof.val := by
  have index0 := Result.ok.inj ((S2W_D189Entry.first_index i.entry).1.symm.trans cuts.proof1Index)
  have index1 := Result.ok.inj ((S2W_D189Entry.first_index i.entry).2.1.symm.trans cuts.public1Index)
  have r0 := cuts.proof1Read
  have r1 := cuts.public1Read
  rw [← index0] at r0
  rw [← index1] at r1
  have raw := (SCE_SnapshotRead.buffer i.entry ops 0 58295 58295 f.raw r0).1
  have pub := (SCE_SnapshotRead.buffer i.entry ops 1 1880 1880 f.pub r1).1
  constructor
  · exact (congrArg bytesOf pub).symm
  · change (bytesOf (i.entry.buffers (i.entry.handles 0).1).val).drop 688 = _
    rw [← raw]
    exact SCE_SuffixShape.drop_eq _ _ cuts.firstSuffix cuts.proofLength

#print axioms submitted_cut
end AspisR1.SCE_FirstCutBytes
end
