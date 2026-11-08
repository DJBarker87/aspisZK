import PV_STX2_SliceMachine
set_option autoImplicit false
namespace PV_LIB_A_UnwindMatch
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Private syntax tags used only by the new cleanup lowering. They are not
source values, allocation images, or initialized bytes. -/
def variantKey (n : Nat) : Data := .object [("PV_LIB_A_MatchVariant",.number n)]
def invalidKey : Data := .object [("PV_LIB_A_MatchInvalid",.boolean true)]
def gapOperator : Data := .object [("PV_LIB_A_MatchGap",.boolean true)]

def key {W : Type} (C : Carrier W Data) (K : Control) (value : Data) : Data → Bool
  | .object [("PV_LIB_A_MatchVariant",.number n)] => K.variant value == some n
  | .object [("PV_LIB_A_MatchInvalid",.boolean true)] => (K.variant value).isNone
  | other => C.matchesKey value other

/-- Match in native unwind syntax is lowered to a switch on the SAME value.
Invalid tags and missing variants take a defined interpretation-gap operator,
which is never a source abort. Every ordinary key/operator uses the old carrier. -/
def operation {W : Type} (C : Carrier W Data) (w : W) : Data → Option Data
  | .object [("PV_LIB_A_MatchGap",.boolean true)] => none
  | other => C.nullary w other

def carrier {W : Type} (C : Carrier W Data) (K : Control) : Carrier W Data :=
  {C with matchesKey := key C K, nullary := operation C}

def gap (site : Site) : Instruction := .bind site (.local 0) (.nullary gapOperator)

def arms (site : Site) (source : List (List Nat × List Instruction)) :
    List (List Data × List Instruction) :=
  ([invalidKey],[gap site]) :: source.map (fun (keys,body) => (keys.map variantKey,body))

def otherwise (site : Site) (source : Option (List Instruction)) : List Instruction :=
  source.getD [gap site]

theorem variant_key {W : Type} (C : Carrier W Data) (K : Control) (value : Data) (n : Nat) :
    (carrier C K).matchesKey value (variantKey n) = (K.variant value == some n) := rfl

theorem invalid_key {W : Type} (C : Carrier W Data) (K : Control) (value : Data) :
    (carrier C K).matchesKey value invalidKey = (K.variant value).isNone := rfl

theorem gap_operator {W : Type} (C : Carrier W Data) (K : Control) (w : W) :
    (carrier C K).nullary w gapOperator = none := rfl

/-- All source address, reference and aggregate operations are unchanged. -/
theorem fields {W : Type} (C : Carrier W Data) (K : Control) :
    (carrier C K).dereference = C.dereference ∧
    (carrier C K).reference = C.reference ∧
    (carrier C K).field = C.field ∧
    (carrier C K).replaceField = C.replaceField ∧
    (carrier C K).aggregate = C.aggregate := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms variantKey
#print axioms invalidKey
#print axioms gapOperator
#print axioms key
#print axioms operation
#print axioms carrier
#print axioms gap
#print axioms arms
#print axioms otherwise
#print axioms variant_key
#print axioms invalid_key
#print axioms gap_operator
#print axioms fields
end PV_LIB_A_UnwindMatch
