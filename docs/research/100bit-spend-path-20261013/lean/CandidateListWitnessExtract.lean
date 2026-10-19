import R1ListWitnessExtract
import R1CandidateBaseProjection

set_option autoImplicit false
namespace AspisR1.CandidateListWitnessExtract

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase
open AspisPool.AlgorithmicCircleDecoderV7

abbrev E := WideExact
abbrev Tuple := ConcreteBinding.Tuple E
abbrev embed := ExactBaseProjection.embed

/-- Executable arithmetic row permutation; do not call a quotient-selected
candidate enumeration or a noncomputable specification list. -/
def rows (t : Tuple) : Trace E := fun c r => t c (rowEquiv r)

theorem rows_eq_model (t : Tuple) : rows t = SemSource.rowsOf rowEquiv t := rfl

/-- Scan exactly the supplied finite candidate list with the retained checked
single-trace extractor. Returned witnesses are checked against the public spend. -/
def extract (pub : Public M31Exact) (candidates : List Tuple) : Option Wspend :=
  ListWitnessExtract.extractList pub (candidates.map rows)

def scanCount (pub : Public M31Exact) (candidates : List Tuple) : Nat :=
  ListWitnessExtract.scanCount pub (candidates.map rows)

theorem returned_checked (pub : Public M31Exact) (candidates : List Tuple)
    (w : Wspend) (h : extract pub candidates = some w) : checkM31 pub w = true :=
  ListWitnessExtract.returned_checked pub _ w h

theorem returned_valid (pub : Public M31Exact) (candidates : List Tuple)
    (w : Wspend) (h : extract pub candidates = some w) : Rspend pub w :=
  ListWitnessExtract.returned_valid pub _ w h

theorem scanCount_le_length (pub : Public M31Exact) (candidates : List Tuple) :
    scanCount pub candidates ≤ candidates.length := by
  simpa only [scanCount, List.length_map] using
    ListWitnessExtract.scanCount_le_length pub (candidates.map rows)

theorem scanCount_le_100 (pub : Public M31Exact) (candidates : List Tuple)
    (hlen : candidates.length ≤ 100) : scanCount pub candidates ≤ 100 :=
  (scanCount_le_length pub candidates).trans hlen

attribute [local irreducible] ConcreteBinding.candidates

/-- Existing semantic production and base typing for one listed candidate
force success of the actual list scan, rather than just existence of an
unrelated valid witness. Earlier checked members may be returned instead. -/
theorem complete_of_member_production
    (pub : Public M31Exact) (candidates : List Tuple) (t : Tuple)
    (ht : t ∈ candidates) (lam chi : E)
    (hshape : PublicOptionShape.canonical pub)
    (hbase : BaseTyped embed.fieldRange (SemSource.rowsOf rowEquiv t))
    (hproduction : ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi
        (SemSource.rowsOf rowEquiv t) ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) (SemSource.rowsOf rowEquiv t)) :
    ∃ w, extract pub candidates = some w ∧ Rspend pub w := by
  obtain ⟨w0, hsingle, _⟩ := TraceWitnessExtract.complete_of_production pub
    (SemSource.rowsOf rowEquiv t) lam chi hshape hbase hproduction
  have hmem : rows t ∈ candidates.map rows := List.mem_map.mpr ⟨t,ht,rfl⟩
  have hex : ∃ w, TraceWitnessExtract.extract pub (rows t) = some w := by
    exact ⟨w0, hsingle⟩
  obtain ⟨w, hw⟩ := ListWitnessExtract.some_result_of_member pub
    (candidates.map rows) (rows t) hmem hex
  exact ⟨w, hw, returned_valid pub candidates w hw⟩

/-- Completeness consumes exactly the list equality supplied by the executable
joint merge. The retained subfield-descent theorem discharges base typing;
semantic production and copy-link facts remain the terminal obligation. -/
theorem complete_of_typed_candidate_list
    (pub : Public M31Exact) (hshape : PublicOptionShape.canonical pub)
    (S : Fin 29 → Subfield E)
    (hlanes : ∀ l : Fin 29, l.val < 26 → S l = embed.fieldRange)
    (W : Fin 29 → InitialWord E) (htyped : CandidateDescent.WordTyped S W)
    (candidates : List Tuple)
    (hlist : candidates.toFinset = ConcreteBinding.candidates W)
    (lam chi : E)
    (hex : ∃ t ∈ ConcreteBinding.candidates W,
      ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi
        (SemSource.rowsOf rowEquiv t) ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) (SemSource.rowsOf rowEquiv t)) :
    ∃ w, extract pub candidates = some w ∧ Rspend pub w := by
  obtain ⟨t, ht, hproduction⟩ := hex
  have hmem : t ∈ candidates := by
    apply List.mem_toFinset.mp
    rw [hlist]
    exact ht
  have hbase := CandidateBaseProjection.rows_base_typed_of_uniform
    S embed.fieldRange hlanes W htyped t ht rowEquiv
  exact complete_of_member_production pub candidates t hmem lam chi
    hshape hbase hproduction

#print axioms rows
#print axioms extract
#print axioms returned_checked
#print axioms returned_valid
#print axioms scanCount_le_length
#print axioms scanCount_le_100
#print axioms complete_of_member_production
#print axioms complete_of_typed_candidate_list
end AspisR1.CandidateListWitnessExtract
