import S2G_InstalledValues
import S2E_Types

/-! Requested theorem TYPES only. No proof, implementation instance, native
refinement or assumption discharge is claimed. The supplied source evaluators
must be actual source-derived functions, never callbacks chosen for equality.
The state carrier must include native allocation/ownership and ordered effects;
abort-prefix observations require the external execution trace as well. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2I.SessionAStatements
open S2E_Reference.S2E_Reference
abbrev Statement := S2G.Statement
abbrev PE := S2G.PE
abbrev PublicEval (S : Type) := S → Statement →
  Result ((core.result.Result (alloc.vec.Vec U8) PE) × S)
abbrev FirstEval (S : Type) := S → Statement → Slice U8 → Slice U8 → Usize →
  Result ((core.result.Result (alloc.vec.Vec U8) PE) × S)

/-- Desired `full_forest_public_port`: complete Result/state equality for
BOTH statement variants. No payment216 or semantic projection substitution. -/
def FullForestPublicPort {C S : Type} (native : PublicEval S)
    (children : Children C S) : Prop :=
  ∀ state statement, native state statement = children.«public» state statement

/-- Required successful output consequence of that SAME concrete full encoder.
This width/magic fact is additional to full field-by-field serializer identity. -/
def FullForestPublicShape {S : Type} (native : PublicEval S) : Prop :=
  ∀ state statement bytes after,
    native state statement = ok (.Ok bytes,after) →
    bytes.val.length = 1880 ∧ bytes.val.take 4 = [65#u8,83#u8,70#u8,56#u8]

/-- Desired `first_decoded_port`: complete stateful source equality on all
admitted inputs, with all rejected inner errors and their states retained. -/
def ComposedFirstPort {C S : Type} (native : FirstEval S)
    (children : Children C S) : Prop :=
  ∀ state statement publicInput proof split,
    native state statement publicInput proof split =
      children.first state statement publicInput proof split

/-- The exact installed first value to be derived from the SAME stateful run.
The actual release None is already inside S2G.first; no callee-wide1768 claim. -/
def ComposedFirstValue {S : Type} (native : FirstEval S)
    (ops : AspisS2OwnedStage1.SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops) : Prop :=
  ∀ state statement publicInput proof split cp after,
    native state statement publicInput proof split = ok (.Ok cp,after) →
      S2G.first ops vops statement publicInput proof split = ok (.Ok cp)

#check FullForestPublicPort
#check FullForestPublicShape
#check ComposedFirstPort
#check ComposedFirstValue
end AspisR1.S2I.SessionAStatements
