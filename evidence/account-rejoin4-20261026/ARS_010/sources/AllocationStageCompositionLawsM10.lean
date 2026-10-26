import AllocationStageSpecM10

set_option autoImplicit false
namespace AspisR1.AllocationStageCompositionLawsM10
open AllocationStageSpecM10

/-- Transport in a work index preserves the counted cells and bits. -/
theorem transport_counts {W x y : Nat} (h : x = y) (a : Allocation W x) :
    (h ▸ a).elements = a.elements ∧ (h ▸ a).bits = a.bits := by
  cases h
  exact ⟨rfl,rfl⟩

/-- A projection-friendly constructor: counters are defined before proofs,
so count equations do not transport a dependent allocation structure. -/
def compose {A B C : Type} {W : Nat} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec W f I J F) (t : StageSpec W g J K G) :
    StageSpec W (fun a => (f a).bind g) I K (fun L => F L+G L+1) where
  toStageSpec := AbstractStageSpecM10.seq s.toStageSpec t.toStageSpec
  allocation a := {
    elements := (s.allocation a).elements+
      (match (s.run a).1 with | none => 0 | some b => (t.allocation b).elements)+1
    bits := (s.allocation a).bits+
      (match (s.run a).1 with | none => 0 | some b => (t.allocation b).bits)+W
    width_law := by
      have hs := (s.allocation a).width_law
      cases h : (s.run a).1 with
      | none => dsimp only; nlinarith
      | some b => have ht := (t.allocation b).width_law; dsimp only; nlinarith
    creation_work := by
      have hs := (s.allocation a).creation_work
      change _ ≤ (PublicParserWork.bind (s.run a) t.run).2
      cases h : (s.run a).1 with
      | none => simp only [h,PublicParserWork.bind]; omega
      | some b =>
        have ht := (t.allocation b).creation_work
        simp only [h,PublicParserWork.bind]
        omega }

/-- On success, both stages' events and the bind-result cell are counted. -/
theorem success {A B C : Type} {W : Nat} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec W f I J F) (t : StageSpec W g J K G) (a : A) (b : B)
    (h : (s.run a).1 = some b) :
    ((compose s t).allocation a).elements = (s.allocation a).elements+(t.allocation b).elements+1 ∧
    ((compose s t).allocation a).bits = (s.allocation a).bits+(t.allocation b).bits+W := by
  simp only [compose,h,and_self]

/-- On failure, the second stage has no allocation contribution. -/
theorem failure {A B C : Type} {W : Nat} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec W f I J F) (t : StageSpec W g J K G) (a : A)
    (h : (s.run a).1 = none) :
    ((compose s t).allocation a).elements = (s.allocation a).elements+1 ∧
    ((compose s t).allocation a).bits = (s.allocation a).bits+W := by
  simp only [compose,h,Nat.add_zero,and_self]

#print axioms transport_counts
#print axioms success
#print axioms failure
end AspisR1.AllocationStageCompositionLawsM10
