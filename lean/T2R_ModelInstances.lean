import Par_Parameters
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_ModelInstances

/-- The original model's LinearMaps supply both families with no separate law
premise. This establishes no native arithmetic or source/public association. -/
theorem functional (i : R1FinalSoundness.SourceInputs)
    (x y : Fin 1024 → LiteralTranscript.E) (a : LiteralTranscript.E) :
    ((∀ j : Fin 6, i.data.F j (x+y) = i.data.F j x+i.data.F j y) ∧
      i.data.F0 (x+y) = i.data.F0 x+i.data.F0 y) ∧
    ((∀ j : Fin 6, i.data.F j (a • x) = a • i.data.F j x) ∧
      i.data.F0 (a • x) = a • i.data.F0 x) :=
  ⟨Par_Parameters.input_map_add i x y,Par_Parameters.input_map_smul i a x⟩

#print axioms functional
end AspisR1.T2R_ModelInstances
end
