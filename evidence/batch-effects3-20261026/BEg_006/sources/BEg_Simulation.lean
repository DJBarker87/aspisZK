import BEg_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Simulation
open Aeneas Aeneas.Std Result SdkC_Source

def value {A B : Type} (decode : A → Option B) : Result A → Option B
  | .ok a => decode a
  | _ => none

def observation {S A B : Type} (decode : A → Option B) (out : Result A × S × Log) :
    Option B × S × Log := (value decode out.1,out.2)

/-- Source-level simulation. Read addresses are literally the same and all
successful replies retain a related continuation. Pure failures may change
error kind; they cannot invent a read or a carrier transition. -/
inductive Related {A B V : Type} (left : A → Option V) (right : B → Option V) :
    Code A → Code B → Prop where
  | done (a : A) (b : B) (same : left a = right b) : Related left right (.done a) (.done b)
  | pure (a : Result A) (b : Result B) (same : value left a = value right b) :
      Related left right (CheckpointBytes5Effect.liftResult a) (CheckpointBytes5Effect.liftResult b)
  | leftStep {C : Type} (a : C) (k : C → Code A) (r : Code B)
      (next : Related left right (k a) r) : Related left right (.step (.ok a) k) r
  | rightStep {C : Type} (a : C) (l : Code A) (k : C → Code B)
      (next : Related left right l (k a)) : Related left right l (.step (.ok a) k)
  | read (parts : Parts) (l : Digest → Code A) (r : Digest → Code B)
      (next : ∀ digest, Related left right (l digest) (r digest)) :
      Related left right (.read parts l) (.read parts r)

/-- Exact mutable-carrier and ordered attempted-log transport, including a
failed or diverging final syscall. This supplies a proof rule, not its native
batch instance. -/
theorem transport {S A B V : Type} (left : A → Option V) (right : B → Option V)
    (l : Code A) (r : Code B) (related : Related left right l r)
    (call : Parts → S → Result Digest × S) (state : S) (before : Log) :
    observation left (BEf_Carrier.run call l state before) =
      observation right (BEf_Carrier.run call r state before) := by
  induction related generalizing state before with
  | done a b same => exact Prod.ext same rfl
  | pure a b same =>
    cases a <;> cases b <;>
      simpa only [CheckpointBytes5Effect.liftResult,BEf_Carrier.run,observation,value] using
        (Prod.ext same (rfl : (state,before) = (state,before)))
  | leftStep a k r next ih => exact ih state before
  | rightStep a l k next ih => exact ih state before
  | read parts l r next ih =>
    unfold BEf_Carrier.run
    cases h : call parts state with
    | mk answer after =>
      simp only []
      cases answer with
      | ok digest => exact ih digest after (before ++ [⟨parts,.ok digest⟩])
      | fail error => rfl
      | div => rfl

#print axioms transport
end AspisR1.BEg_Simulation
end
