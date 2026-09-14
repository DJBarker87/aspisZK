import FSV8S7PreAlphaConcreteOrdinaryCut
import FSV8S5WordCovectorPolynomial

/-!
# Source-cut base ordinary covector

The base covector is computed from the existing source cut's actual `z`,
prepared scales, chord coefficients, and the frozen inactive-mask table.  A
reference word remains explicit until an authenticated prefix-derived family
supplies it.  The separate image functional is not included here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.S8CutBaseCovector
open FSV8S7PreAlphaConcreteOrdinaryCut SameBodyFunctionalProducerSource
open SameBodySourceRelationProducer
noncomputable section
abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K

def originalWeight {body : Bytes} (cut : Cut body) (index : Fin 1024) : K :=
  let group := inactiveGroups.getD (index.val / 16) 0
  let mask := inactiveMasks.getD group 0
  let bit := (mask / 2^(index.val % 16)) % 2
  let points := SameBodyPublicCorrection.points ordinaryOps cut.semantic.z
  (List.finRange 3).foldl (fun total r =>
    total + (List.finRange 10).foldl (fun acc j =>
      acc * (if (index.val / 2^(9-j.val)) % 2 = 0
        then 1 - points r j else points r j))
      (cut.functional.value.prepared.scales r)) (if bit=0 then 0 else 1)

def trailingOnes : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, index => if index%2=0 then 0 else 1 + trailingOnes fuel (index/2)

/-- Closed finite carry-row formula for the source `xt` loop. -/
def xtEntry (v : List K) (j : Nat) : K :=
  let t := trailingOnes 10 j
  ((List.range t).map (fun k =>
    (1/2 : K)^(k+1) * v.getD (j-(2^(k+1)-1)) 0)).sum +
      (1/2 : K)^t * v.getD (j+1) 0

def baseWeight {body : Bytes} (cut : Cut body) : Fin 1024 → K :=
  let w := List.ofFn (originalWeight cut) ++ List.replicate 4 0
  let even := (List.range 514).map (fun j => w.getD (2*j) 0)
  let odd := (List.range 514).map (fun j => w.getD (2*j+1) 0)
  let xeven := (List.range 513).map (xtEntry even)
  let abc := cut.functional.value.prepared.abc
  fun i =>
    let j := i.val/2
    if i.val%2=0 then
      abc 0 * even.getD j 0 + abc 1 * xtEntry even j + abc 2 * odd.getD j 0
    else abc 2 * (even.getD j 0 - xtEntry xeven j) +
      abc 0 * odd.getD j 0 + abc 1 * xtEntry odd j

/-- The word is deliberately explicit; it must come from a prefix-derived
candidate family in the source consumer. -/
def baseChunks {body : Bytes} (cut : Cut body) (word : Fin 1024 → K) :
    List (FSV8S5WordCovectorPolynomial.Quad K × FSV8S5WordCovectorPolynomial.Quad K) :=
  List.ofFn (fun j : Fin 256 =>
    ((fun i : Fin 4 => word ⟨4*j.val+i.val, by omega⟩),
     (fun i : Fin 4 => baseWeight cut ⟨4*j.val+i.val, by omega⟩)))

theorem baseChunks_length {body : Bytes} (cut : Cut body) (word : Fin 1024 → K) :
    (baseChunks cut word).length = 256 := by
  simp only [baseChunks, List.length_ofFn]

def baseReference {body : Bytes} (cut : Cut body) (word : Fin 1024 → K) :
    FSV8S5CompactPolynomialTarget.Coeff7 K :=
  FSV8S5WordCovectorPolynomial.wordCoefficients (1/4 : K) (baseChunks cut word)

#print axioms baseChunks_length
end
end AspisV8Completion.S8CutBaseCovector
