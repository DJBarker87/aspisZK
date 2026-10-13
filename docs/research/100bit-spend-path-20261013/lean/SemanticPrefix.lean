import R1SemanticCandidateList
import R1SemanticHit
import R0P.MaskEarly
import R0P.MaskDensity

/-! Reuse only the first 25 masked semantic rows. The old classifier's
pre-C2 padding argument covers the literal R1 list without fixing H1/G
before lambda or chi. No old opening tail or Fiat--Shamir theorem is used.
Parsing, authenticated-word correspondence and absence of a prefix hit
remain explicit; this file does not give a shared-oracle probability law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticPrefix
open R0P R0P.SemSource R0P.Mask R0P.SemRounds R0C.SemStatement Polynomial
open AspisCircleGroupOrder AspisPool.AlgorithmicCircleDecoderV7

attribute [local irreducible] AspisR0.ListsResponses.Lambda LambdaRows
  AspisR1.InitialResponses.Lambda ConcreteBinding.candidates

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

theorem slice_zc (cs : List E) :
    semSlice (fun j : Fin 24 => cs.getD j.val 0) 3 10 =
      preZc (fun j : Fin 14 => cs.getD j.val 0) := by
  funext j
  simp only [semSlice, semPrefixVal, preZc, dif_pos (show 3 + j.val < 24 by omega)]

/-- One no-hit premise on the parsed semantic prefix supplies every exclusion
required by the R1 candidate-level semantic theorem. The prefix ends before
circle/opening rows, so the old five-row opening protocol is not assumed. -/
theorem outsideBad_of_prefix
    {S : Fin 29 → Subfield E} {F : Subfield E} (B : PackBasis F)
    (x : TypedContext E S) (htransport : x.transport = AspisR1.rowEquiv)
    (fallback : AspisR0.ChordGeometry.Point E)
    (rs : List (MsgZ E × ChalZ E)) (hlen : rs.length = 25)
    (cs : List E) (hparse : semChalsZ rs = some cs)
    (claim : E) (hclaim : claimOf rs = some claim)
    (polys : Fin 10 → E[X]) (hpolys : semPolysZ rs = some polys)
    (hdegree : ∀ j, (polys j).natDegree ≤ 27)
    (hw gw : InitialWord E) (hc2 : c2OfZ rs = some (hw, gw))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback (maskClaimsR0 B) B) x [] rs)
    (m : ConcreteBinding.Tuple E)
    (hm : m ∈ ConcreteBinding.candidates (c2Words x hw gw)) :
    MaskedSemantic.OutsideBad x.pub B (rowsOf AspisR1.rowEquiv m)
      (fun j => cs.getD j.val 0) (cs.getD 14 0) claim
      (fun j => cs.getD (15 + j.val) 0) polys := by
  have ht : rowsOf AspisR1.rowEquiv m ∈ LambdaRows x.transport (c2Words x hw gw) := by
    rw [htransport]
    exact SemanticCandidateList.rowsOf_candidate_mem_LambdaRows _ _ _ hm
  have hno' : ¬ hitFrom (sourceDataWithFallbackZ fallback (maskClaimsR0 B) B)
      x [] (rs ++ []) := by simpa only [List.append_nil] using hno
  have hearly := earlyRounds_cover (rowsOf AspisR1.rowEquiv m) x.pub B
    (fun j => cs.getD j.val 0)
    (no_hit_early fallback (maskClaimsR0 B) B x rs [] hlen cs hparse hw gw hc2
      (rowsOf AspisR1.rowEquiv m) ht hno')
  rw [slice_zc] at hearly
  have heta := no_hit_eta fallback (maskClaimsR0 B) B x rs [] hlen cs hparse
    claim hclaim hw gw hc2 (rowsOf AspisR1.rowEquiv m) ht hno'
  have halpha := no_hit_alpha fallback (maskClaimsR0 B) B x rs [] hlen cs hparse
    claim hclaim polys hpolys hdegree hw gw hc2 (rowsOf AspisR1.rowEquiv m) ht hno'
  rw [htransport] at heta halpha
  exact ⟨hearly.1, hearly.2.1, hearly.2.2.1, hearly.2.2.2, heta, halpha⟩

/-- Apply the prefix exclusions directly to the recovered opening witness.
Only the semantic classifier at each actual preceding prefix is excluded.
The C2 and transport equalities are model correspondence obligations, not
assumed semantic correctness of a candidate. -/
theorem large_matching_extracts_of_prefix
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F) (B : PackBasis F)
    (x : TypedContext E S) (htransport : x.transport = AspisR1.rowEquiv)
    (pubTyped : PublicBase F x.pub)
    (d : MatchingSupport.Data E) (typed : CandidateDescent.WordTyped S d.W)
    (fallback : AspisR0.ChordGeometry.Point E)
    (rs : List (MsgZ E × ChalZ E)) (hlen : rs.length = 25)
    (cs : List E) (hparse : semChalsZ rs = some cs)
    (claim : E) (hclaim : claimOf rs = some claim)
    (polys : Fin 10 → E[X]) (hpolys : semPolysZ rs = some polys)
    (hw gw : InitialWord E) (hc2 : c2OfZ rs = some (hw, gw))
    (hwords : d.W = c2Words x hw gw)
    (hexcluded : ∀ i : Fin rs.length, ∀ sm,
      (rs[i.val]'i.isLt).1 = .semantic sm →
        ¬ semanticBadZ (maskClaimsR0 B) B ⟨x, rs.take i.val⟩ sm (cs.getD i.val 0))
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (hgood : MatchingSupport.Good
      (RawOpening.withRows (RingHom.id E)
        (SemanticOpening.rows inactive
          (SemanticTransport.points (fun j => cs.getD (15 + j.val) 0))
          (SemSource.libraWeight (fun j => cs.getD (15 + j.val) 0)) circle) d))
    (haccepted : MatchingSupport.AcceptedPairing
      (RawOpening.withRows (RingHom.id E)
        (SemanticOpening.rows inactive
          (SemanticTransport.points (fun j => cs.getD (15 + j.val) 0))
          (SemSource.libraWeight (fun j => cs.getD (15 + j.val) 0)) circle) d))
    (hcard : 9558 ≤ (MatchingSupport.matchingSet
      (RawOpening.withRows (RingHom.id E)
        (SemanticOpening.rows inactive
          (SemanticTransport.points (fun j => cs.getD (15 + j.val) 0))
          (SemSource.libraWeight (fun j => cs.getD (15 + j.val) 0)) circle) d)).card)
    (checks : sumcheckChecksZ (maskClaimsR0 B) x.pub B
      (fun j => cs.getD j.val 0) (cs.getD 14 0) claim
      (fun j => cs.getD (15 + j.val) 0) polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3)) :
    ∃ m ∈ ConcreteBinding.candidates d.W,
      (ProductionHolds x.pub (cs.getD 0 0) (cs.getD 1 0) (rowsOf AspisR1.rowEquiv m) ∧
        CopyLinkBalance x.pub (rowsOf AspisR1.rowEquiv m)) ∧
      InputNoteExtracted x.pub (rowsOf AspisR1.rowEquiv m) := by
  have hno := (SemanticHit.no_hitFrom_iff_all_semanticBadZ_excluded x fallback
    (maskClaimsR0 B) B rs cs hparse (by omega)).mpr hexcluded
  apply MaskedSemantic.large_matching_extracts prime hprime S F lanesF B x.pub
    pubTyped d typed inactive circle (fun j => cs.getD j.val 0) (cs.getD 14 0)
    claim (fun j => cs.getD (15 + j.val) 0) polys hgood haccepted hcard checks
  intro m hm
  rw [hwords] at hm
  exact outsideBad_of_prefix B x htransport fallback rs hlen cs hparse claim
    hclaim polys hpolys checks.1 hw gw hc2 hno m hm

#print axioms slice_zc
#print axioms outsideBad_of_prefix
#print axioms large_matching_extracts_of_prefix
end AspisR1.SemanticPrefix
end
