import R1Z.ProverCommitNativeEval48
/-! All 29 y1 cells composed symbolically. No reduction of a concrete
29-lane evaluator or a 512-term dot product is used. Coefficient provenance
and the simulator's complete payload remain separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitY1Aggregate48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact
abbrev E := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev Coeff := Nat → Old.Q

def normalizedRun (q : Coeff) (x y : Old.Q) : Result E :=
  ProverCommitNativeEval48.run (fun j => ProverCommitNativeOps47.normalize (q j))
    (ProverCommitNativeOps47.normalize x) (ProverCommitNativeOps47.normalize y)

def value (q : Coeff) (x y : Old.Q) : Old.Q :=
  Classical.choose (ProverCommitNativeEval48.raw_value q x y)

theorem value_spec (q : Coeff) (x y : Old.Q) :
    normalizedRun q x y=ok (ProverCommitNativeOps47.embedded (value q x y)) ∧
    Canonical (value q x y) ∧
    decode (value q x y)=ProverCommitEval47.messageEval
      (fun j : Fin 1024 => decode (q j.val)) (decode x) (decode y) :=
  Classical.choose_spec (ProverCommitNativeEval48.raw_value q x y)

attribute [local irreducible] value normalizedRun ProverCommitEval47.messageEval

def cell (q : Coeff) (x y : Old.Q) : Fin 32 → UInt8 :=
  ProverCommitLimbBytes47.sourceCell (value q x y) (value_spec q x y).2.1

theorem cell_image (q : Coeff) (x y : Old.Q) :
    cell q x y=ProverCommitValueRange47.bytes (ProverCommitY1Bytes47.model q x y) := by
  rw [cell,ProverCommitLimbBytes47.source_image]
  apply congrArg ProverCommitValueRange47.bytes
  rw [ProverCommitY1Bytes47.model,ProverCommitEval47.message_embed]
  rw [(value_spec q x y).2.2]

def evaluations (x y : Old.Q) : List Coeff → Result (List E)
 | [] => ok []
 | q::qs => do
   let z ← normalizedRun q x y
   let zs ← evaluations x y qs
   ok (z::zs)

theorem evaluations_exact (x y : Old.Q) (qs : List Coeff) :
    evaluations x y qs=ok (qs.map (fun q => ProverCommitNativeOps47.embedded (value q x y))) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [evaluations,(value_spec q x y).1,ih,bind_tc_ok,List.map_cons]

def encoded (qs : List Coeff) (x y : Old.Q) : List UInt8 :=
  (qs.map (fun q => List.ofFn (cell q x y))).flatten

def modelEncoded (qs : List Coeff) (x y : Old.Q) : List UInt8 :=
  (qs.map (fun q => List.ofFn (ProverCommitValueRange47.bytes (ProverCommitY1Bytes47.model q x y)))).flatten

theorem encoded_image (qs : List Coeff) (x y : Old.Q) :
    encoded qs x y=modelEncoded qs x y := by
  simp only [encoded,modelEncoded,cell_image]

def lanes (q : Fin 29 → Coeff) : List Coeff := List.ofFn q

theorem every_lane (q : Fin 29 → Coeff) (x y : Old.Q) :
    evaluations x y (lanes q)=
      ok ((lanes q).map (fun c => ProverCommitNativeOps47.embedded (value c x y))) ∧
    encoded (lanes q) x y=modelEncoded (lanes q) x y :=
  ⟨evaluations_exact x y (lanes q),encoded_image (lanes q) x y⟩

theorem byte_count (q : Fin 29 → Coeff) (x y : Old.Q) :
    (encoded (lanes q) x y).length=29*32 := by
  unfold encoded
  rw [List.length_flatten]
  simp only [List.map_map,List.length_ofFn,Function.comp_def,List.map_const',List.sum_replicate,
    lanes,List.length_ofFn]
  rfl

#print axioms value_spec
#print axioms cell_image
#print axioms evaluations_exact
#print axioms encoded_image
#print axioms every_lane
#print axioms byte_count
end R1Z.ProverCommitY1Aggregate48
