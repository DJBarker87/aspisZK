import XRk_DotModel
import LPh_RawSpec
import LPg_Scanners
import LPg_Validation
import LPc_ExpandRows
import LPc_DecodeSuccess
set_option autoImplicit false
namespace AspisR1.LPh.Model
open Aeneas Aeneas.Std Result

def packed (a b c d : U32) : XRk_Release.fast_pairing.canonical.Q :=
  Array.make 4#usize [a,b,c,d]

/-- Independent model-side port to the shared Nat specification. The native
port is LPh.Raw.raw_nat; their generated contexts cannot yet be imported together. -/
theorem raw_words (a b c d e f g h : U32) :
    XRk_raw (packed a b c d) (packed e f g h)=
      RawSpec.rawNat a.val b.val c.val d.val e.val f.val g.val h.val := rfl

/-- The scanner association contract is satisfiable for every input, including
rejected prefixes. This constructs a MODEL callback, not a native installation. -/
theorem scanner_contract_inhabited (bs : List U8) (k : Bool) (size : bs.length=928) :
    ∃ step : Bool → Nat → Bool,
      (∀ good i, i<29 → step good i=(good && LPa.Echeck.predicate bs k i)) ∧
      LPa.stages step true 29=LPa.Echeck.loop bs k := by
  refine ⟨fun good i => good && LPa.Echeck.predicate bs k i,?_,?_⟩
  · intro good i hi; rfl
  · exact LPg.echeck_stages bs k size _ (by intro good i hi; rfl)

theorem canonical_domain_inhabited :
    ∃ a b : U32, a.val=0 ∧ b.val=1 ∧ a.val<2147483647 ∧ b.val<2147483647 := by
  refine ⟨0#u32,1#u32,rfl,rfl,?_,?_⟩
  · change (0 : Nat)<2147483647; omega
  · change (1 : Nat)<2147483647; omega

#print axioms raw_words
#print axioms scanner_contract_inhabited
#print axioms canonical_domain_inhabited
#print axioms LPg.echeck_stages
#print axioms LPg.check_stages
#print axioms LPg.validation_error
#print axioms LPc.Expand.row_low
#print axioms LPc.Expand.row_high
end AspisR1.LPh.Model
