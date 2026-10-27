import RPz7_F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Carried
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier

def Carried {F C : Type} (c : DrvC_Installation.Configuration F C) (i : F3_Model.Input) : Prop :=
  ∃ s : Submission,i.semantic=(input c s).semantic ∧ i.physical=(input c s).physical ∧
    i.stored=s.stored ∧ ∀ row,LiteralTranscript.erase (i.proof row)=LiteralTranscript.erase ((input c s).proof row)

theorem input_carried {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) :
    Carried c (input c s) := ⟨s,rfl,rfl,rfl,fun _=>rfl⟩

theorem lift_carried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (H : Bytes → State) : Carried c (eval H (lift c P)).2 := by
  rw [lift_eval];exact input_carried c _

theorem enrich_carried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (w : CanonicalCutEnrichedTranscript.Words) (i : F3_Model.Input) (h : Carried c i) :
    Carried c (enrich w i) := by
  obtain ⟨s,semantic,physical,stored,rows⟩ := h
  refine ⟨s,semantic,physical,stored,fun row=>?_⟩
  exact (CanonicalCutEnrichedTranscript.erase_enrichMessage w (i.proof row)).trans (rows row)

theorem canon_carried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (i : F3_Model.Input) (h : Carried c i) : Carried c (F3T_Canon.canonInput i) := by
  obtain ⟨s,semantic,physical,stored,rows⟩ := h
  exact ⟨s,semantic,physical,stored,fun row=>(R16CanonReduction.erase_proof i.proof row).trans (rows row)⟩

theorem canon_lift_carried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (H : Bytes → State) : Carried c (eval H (F3T_Canon.canon (lift c P))).2 := by
  rw [F3T_Canon.canon_eval];exact canon_carried c _ (lift_carried c P H)

#print axioms input_carried
#print axioms lift_carried
#print axioms enrich_carried
#print axioms canon_carried
#print axioms canon_lift_carried
end AspisR1.F3T_Carried
end
