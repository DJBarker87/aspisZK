import VTop_Flow
set_option autoImplicit false
namespace AspisR1.VTop_Erasure
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Flow
theorem erase_pure (ops : Ops) {A : Type} (a : A) :
    erase ops (pure a) = ok a := rfl

theorem erase_liftM (ops : Ops) {A : Type} (r : Result A) :
    erase ops (monadLift r : Code A) = r := erase_lift ops r

theorem erase_if (ops : Ops) {A : Type} (p : Prop) [Decidable p]
    (yes no : Code A) : erase ops (if p then yes else no) =
      if p then erase ops yes else erase ops no := by split <;> rfl

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)


theorem tx1_source (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit)) :
    VTop_Flow.tx1 (sourceEffects ops) D semantic pub proof split hash obs =
      verifier.candidate.tx1 ops D semantic pub proof split hash obs := rfl

theorem tx1_erasure (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit)) :
    erase ops (VTop_Flow.tx1 traceEffects D semantic pub proof split hash obs) =
      verifier.candidate.tx1 ops D semantic pub proof split hash obs := by
  simp only [VTop_Flow.tx1, verifier.candidate.tx1, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if])
    | (apply bind_congr; intro x)
    | split
#print axioms tx1_source
#print axioms tx1_erasure

theorem tx2_common_source (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    VTop_Flow.tx2_common (sourceEffects ops) D pub proof checkpoint hash obs =
      verifier.candidate.tx2_common ops D pub proof checkpoint hash obs := rfl

theorem tx2_common_erasure (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    erase ops (VTop_Flow.tx2_common traceEffects D pub proof checkpoint hash obs) =
      verifier.candidate.tx2_common ops D pub proof checkpoint hash obs := by
  simp only [VTop_Flow.tx2_common, verifier.candidate.tx2_common, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if])
    | (apply bind_congr; intro x)
    | split
#print axioms tx2_common_source
#print axioms tx2_common_erasure

theorem tx2_authenticated_source (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    VTop_Flow.tx2_authenticated (sourceEffects ops) D pub proof checkpoint hash obs =
      verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs := rfl

theorem tx2_authenticated_erasure (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    erase ops (VTop_Flow.tx2_authenticated traceEffects D pub proof checkpoint hash obs) =
      verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs := by
  simp only [VTop_Flow.tx2_authenticated, verifier.candidate.tx2_authenticated, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if, VTop_Flow.tx2_common, verifier.candidate.tx2_common]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if, VTop_Flow.tx2_common, verifier.candidate.tx2_common])
    | (apply bind_congr; intro x)
    | split
#print axioms tx2_authenticated_source
#print axioms tx2_authenticated_erasure
#print axioms erase_pure
#print axioms erase_liftM
#print axioms erase_if
#print axioms bind_congr
end AspisR1.VTop_Erasure
