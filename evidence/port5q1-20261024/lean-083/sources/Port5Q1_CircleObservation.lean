import Port5Q1_ObservedOpening
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_CircleObservation
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open CheckpointBytes5Output (ofE)
abbrev FE := OraclePortCheckpointAbiC5.E

structure SessionAComparison (ops : Ops) : Prop where
  unequal : ∀ x y, core.cmp.PartialEq.ne.trait_default ops.widePartialEq x y=ok false → ofE x=ofE y

/-- Bind the actual returned circle fold to the SAME selected V symbol using
the actual successful comparison and actual modulo-four array read. This is
not a first-fold/dot implementation instance or a proof of match0. -/
theorem selected (ops : Ops) (comparison : SessionAComparison ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation ops proof p a out g obs geometry b bout)
    (query : Fin 262144) (V : Fin 262144 → FE)
    (raw : o.query.val=query.val)
    (quartet : ∀ t, Port5Q1_OpeningValues.values o.values t=
      V (AspisR1.childIndex (AspisR1.parentIndex (n:=65536) query) t)) :
    ofE o.folded=V query := by
  have castEq : o.u=UScalar.cast .Usize o.query := (Result.ok.inj o.cast).symm
  have uv : o.u.val=query.val := by
    rw [castEq,UScalar.cast_val_eq,raw]
    apply Nat.mod_eq_of_lt
    have bound := query.isLt
    have cap : 262144≤UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
    simpa only [UScalar.size_def] using Nat.lt_of_lt_of_le bound cap
  obtain ⟨rem,remRun,selectedRun⟩ := o.selected_read
  obtain ⟨actual,run,value⟩ := WP.spec_imp_exists (UScalar.rem_spec o.u (y:=4#usize) (by decide))
  have same : actual=rem := Result.ok.inj (run.symm.trans remRun)
  have rv : rem.val=query.val%4 := by rw [←same]; simpa only [uv] using value
  have rb : rem.val<4 := by rw [rv]; omega
  obtain ⟨actual,run,contents⟩ := WP.spec_imp_exists (Array.index_usize_spec o.values rem (by change rem.val<o.values.val.length; rw [o.values.property]; exact rb))
  have same : actual=o.selected := Result.ok.inj (run.symm.trans selectedRun)
  let slot : Fin 4 := ⟨rem.val,rb⟩
  have selectedEq : Port5Q1_OpeningValues.values o.values slot=ofE o.selected := by
    unfold Port5Q1_OpeningValues.values
    rw [List.getElem?_eq_getElem (by rw [o.values.property]; exact rb),Option.getD_some]
    exact congrArg ofE (contents.symm.trans same)
  have child : AspisR1.childIndex (AspisR1.parentIndex (n:=65536) query) slot=query := by
    apply Fin.ext
    change 4*(query.val/4)+rem.val=query.val
    rw [rv]
    omega
  rw [comparison.unequal _ _ o.comparison,←selectedEq,quartet slot,child]

#print axioms selected
end AspisR1.Port5Q1_CircleObservation
end
