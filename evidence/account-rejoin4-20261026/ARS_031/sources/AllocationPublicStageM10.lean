import ExtractorStagesM10

set_option autoImplicit false
namespace AspisR1.AllocationPublicStageM10

def cells {A B : Type} (parsed : Option B × Nat) (words : A × Nat)
    (heapWords heapParse : Nat) (heapPost : B → A → Nat) : Nat :=
  heapWords+heapParse+(match parsed.1 with | none => 0 | some pub => heapPost pub words.1)+1+32

theorem paid {A B C : Type} (parsed : Option B × Nat) (words : A × Nat)
    (post : B → A → Option C × Nat) (heapWords heapParse : Nat) (heapPost : B → A → Nat)
    (hw : heapWords ≤ words.2) (hp : heapParse ≤ parsed.2)
    (hc : ∀ pub w, heapPost pub w ≤ (post pub w).2) :
    cells parsed words heapWords heapParse heapPost ≤ (ExtractorStagesM10.publicStage words parsed post).2 := by
  cases h : parsed.1 with
  | none => simp only [cells,ExtractorStagesM10.publicStage,PublicParserWork.bind,h]; omega
  | some pub =>
    have hh := hc pub words.1
    simp only [cells,ExtractorStagesM10.publicStage,PublicParserWork.bind,h]
    omega

#print axioms paid
end AspisR1.AllocationPublicStageM10
