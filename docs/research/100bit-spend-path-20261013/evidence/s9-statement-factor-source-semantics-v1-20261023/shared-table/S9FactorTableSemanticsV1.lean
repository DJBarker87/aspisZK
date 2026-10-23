import S9FactorNestedWriteV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ConstructorV3QMMulSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FactorTableSemanticsV1
open AspisR1S9FactorArrayEntryV1 AspisR1S9FactorNestedWriteV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
abbrev ExactQM := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
abbrev Table := Nat → Nat → Nat → ExactQM

def value (factors : Factors) (k d i : Usize)
    (hk : k.val < 5) (hd : d.val < 5) (hi : i.val < 4) : ExactQM :=
  decode (atN (atN (atN factors k hk) d hd) i hi)

def Meaning (factors : Factors) (model : Table) : Prop :=
  ∀ (k d i : Usize) (hk : k.val < 5) (hd : d.val < 5) (hi : i.val < 4),
    value factors k d i hk hd hi = model k.val d.val i.val

def rawTable (factors : Factors) (k d i : Nat) : ExactQM :=
  match factors.val[k]? with
  | none => 0
  | some row => match row.val[d]? with
    | none => 0
    | some cell => match cell.val[i]? with
      | none => 0
      | some q => decode q

private theorem lookup_atN {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (hi : i.val < N.val) : a.val[i.val]? = some (atN a i hi) := by
  unfold atN
  exact List.getElem?_eq_getElem (by simpa [a.property] using hi)

theorem rawTable_meaning (factors : Factors) : Meaning factors (rawTable factors) := by
  intro k d i hk hd hi
  unfold value rawTable
  simp only [lookup_atN factors k hk, lookup_atN (atN factors k hk) d hd,
    lookup_atN (atN (atN factors k hk) d hd) i hi]

def write (model : Table) (k d : Nat) (written : Nat → ExactQM) : Table :=
  fun k' d' i' => if k'=k then if d'=d then written i' else model k' d' i'
    else model k' d' i'

/-- The actual row mutation transports full decoded table meaning, including
all untouched factor entries. No source arithmetic behavior is assumed. -/
theorem accepted_write_meaning
    (factors : Factors) (model : Table) (k d : Usize) (old rowOut : Row)
    (back : Row → Factors) (cell : Cell) (written : Nat → ExactQM)
    (hk : k.val < 5) (hd : d.val < 5)
    (hm : Meaning factors model)
    (hc : ∀ (i : Usize) (hi : i.val < 4), decode (atN cell i hi) = written i.val)
    (hmut : Array.index_mut_usize factors k = .ok (old,back))
    (hrow : Array.update old d cell = .ok rowOut) :
    Meaning (back rowOut) (write model k.val d.val written) := by
  intro k' d' i' hk' hd' hi'
  have hf := accepted_nested_write factors k d k' d' old rowOut back cell
    hk hd hk' hd' hmut hrow
  have hv := congrArg (fun c : Cell => decode (atN c i' hi')) hf
  change value (back rowOut) k' d' i' hk' hd' hi' = _ at hv
  by_cases he : k'.val=k.val
  · by_cases he' : d'.val=d.val
    · simp only [if_pos he,if_pos he'] at hv
      simpa only [write,if_pos he,if_pos he'] using hv.trans (hc i' hi')
    · simp only [if_pos he,if_neg he'] at hv
      have hold := hm k d' i' hk hd' hi'
      change decode (atN (atN (atN factors k hk) d' hd') i' hi') = _ at hold
      simpa only [write,if_pos he,if_neg he',he,ite_self] using hv.trans hold
  · simp only [if_neg he] at hv
    simpa only [write,if_neg he] using hv.trans (hm k' d' i' hk' hd' hi')

#print axioms rawTable_meaning
#print axioms accepted_write_meaning
end AspisR1S9FactorTableSemanticsV1
