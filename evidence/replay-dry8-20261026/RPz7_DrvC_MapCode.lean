import RPz7_DrvC_OraclePort
import RPz7_DrvC_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_MapCode
open Aeneas Aeneas.Std Result
open DrvC_Program

theorem bind_map {A B C : Type} (f : A → B) (p : SdkC_Source.Code A)
    (k : B → SdkC_Source.Code C) :
    (mapCode f p >>= k) = (p >>= fun a => k (f a)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    change CheckpointBytes5Effect.Code.step r _ = CheckpointBytes5Effect.Code.step r _
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    change CheckpointBytes5Effect.Code.read parts _ = CheckpointBytes5Effect.Code.read parts _
    congr 1
    funext a
    exact ih a

theorem map_bind {A B C : Type} (f : B → C) (p : SdkC_Source.Code A)
    (k : A → SdkC_Source.Code B) :
    mapCode f (p >>= k) = (p >>= fun a => mapCode f (k a)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    change CheckpointBytes5Effect.Code.step r _ = CheckpointBytes5Effect.Code.step r _
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    change CheckpointBytes5Effect.Code.read parts _ = CheckpointBytes5Effect.Code.read parts _
    congr 1
    funext a
    exact ih a

theorem map_as_bind {A B : Type} (f : A → B) (p : SdkC_Source.Code A) :
    mapCode f p = (p >>= fun a => pure (f a)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    change CheckpointBytes5Effect.Code.step r _ = CheckpointBytes5Effect.Code.step r _
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    change CheckpointBytes5Effect.Code.read parts _ = CheckpointBytes5Effect.Code.read parts _
    congr 1
    funext a
    exact ih a

theorem map_comp {A B C : Type} (f : A → B) (g : B → C) (p : SdkC_Source.Code A) :
    mapCode g (mapCode f p) = mapCode (g ∘ f) p := by
  induction p with
  | done a => rfl
  | step r next ih =>
    simp only [mapCode]
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    simp only [mapCode]
    congr 1
    funext a
    exact ih a

#print axioms bind_map
#print axioms map_bind
#print axioms map_as_bind
#print axioms map_comp
end AspisR1.DrvC_MapCode
end
