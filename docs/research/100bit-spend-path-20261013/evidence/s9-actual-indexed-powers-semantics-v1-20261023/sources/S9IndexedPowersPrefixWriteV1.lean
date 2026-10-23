import S9ActualIndexedPowersArithmeticV1
import S9ConstructorV3Loop2InnerCanonicalV1
import Query31ArrayReadback
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9IndexedPowersPrefixWriteV1
open AspisR1S9ActualPairWideCanonicalV1
open AspisR1S9ActualIndexedPowersArithmeticV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev WA := Array W 4#usize

def Prefix (x : W) (a : WA) (upto : Nat) : Prop :=
  ∀ (j : Usize) (value : W), Array.index_usize a j = .ok value → j.val < upto →
    decode value = decode x ^ j.val

/-- One SAME successful native mutable-array write extends the decoded-power
prefix by exactly its current cell. Other earlier reads are unchanged; no
canonicality or equality of the unwritten tail is needed. -/
theorem write_extends_power_prefix (x : W) (a : WA) (i : Usize)
    (old p : W) (back : W → WA)
    (hmut : Array.index_mut_usize a i = .ok (old,back))
    (hp : decode p = decode x ^ i.val) (ha : Prefix x a i.val) :
    Prefix x (back p) (i.val+1) := by
  have hi := index_mut_bound a i old back hmut
  have hback := index_mut_back_set a i old back hi hmut
  have hlen : i.val < a.length := by simpa only [a.property] using hi
  obtain ⟨updated,hu,hupdated⟩ := WP.spec_imp_exists (Array.update_spec a i p hlen)
  have he : updated = back p := by
    calc
      updated = a.set i p := hupdated
      _ = back p := by rw [hback]
  have hu' : Array.update a i p = .ok (back p) := by simpa only [he] using hu
  intro j value hread hj
  have hjbound := index_success_bound (back p) j value hread
  by_cases hji : j = i
  · subst j
    have hwrite := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
      a i p hi (back p) hu'
    have hv : p = value := Result.ok.inj (hwrite.symm.trans hread)
    subst value
    exact hp
  · have hneq : i ≠ j := Ne.symm hji
    have hsame := AspisR1PublicPreparation.Query31SourceSchedule.update_readback_other
      a i j p hneq hi hjbound (back p) hu'
    have hreadOld : Array.index_usize a j = .ok value := hsame.symm.trans hread
    have hneqval : j.val ≠ i.val := by
      intro hval
      exact hji (UScalar.eq_of_val_eq hval)
    have hjold : j.val < i.val := by omega
    exact ha j value hreadOld hjold

#print axioms write_extends_power_prefix
end AspisR1S9IndexedPowersPrefixWriteV1
