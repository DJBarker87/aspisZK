import R0P.MaskProtocol

/-! Parsers for 25 semantic rows, two circle rows and five opening rows.
Eta's mask-sum message is at index 14; alpha polynomials start at 15. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 R0C.SemStatement R0P.SemSource Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisR0.Chord AspisR0.ChordGeometry AspisWide.InitialEncoder
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K]

def unmaskSem : SemMsgZ K → SemMsg K
  | .base m => m
  | .maskSum _ => .none

def unmaskMsg : MsgZ K → Msg K K (SemMsg K)
  | .semantic m => .semantic (unmaskSem m)
  | .beforeZ0 y => .beforeZ0 y
  | .beforeZ1 y => .beforeZ1 y
  | .opening m => .opening m

def baseRoundsZ (rs : List (MsgZ K × ChalZ K)) :=
  rs.map (fun q => (unmaskMsg q.1, q.2))

def c2OfZ (rs : List (MsgZ K × ChalZ K)) := c2Of (baseRoundsZ rs)

def claimOf (rs : List (MsgZ K × ChalZ K)) : Option K :=
  match (rs[14]? : Option (MsgZ K × ChalZ K)) with
  | some (.semantic (.maskSum claim), _) => some claim
  | _ => none

def semChalsZ : List (Msg K K (SemMsgZ K) × Chal K K) → Option (List K)
  | [] => some []
  | (.semantic _, .semantic c) :: rest => (semChalsZ rest).map (c :: ·)
  | _ => Option.none

/-- The opening rounds, all of the opening kind. -/
def openingRoundsZ : List (Msg K K (SemMsgZ K) × Chal K K) →
    Option (List (R0FS.Msg K × R0FS.Chal K))
  | [] => some []
  | (.opening om, .opening oc) :: rest => (openingRoundsZ rest).map ((om, oc) :: ·)
  | _ => Option.none

theorem semChalsZ_of_pairs (rs : List (SemMsgZ K × K)) :
    semChalsZ (rs.map (fun q => (Msg.semantic q.1, Chal.semantic q.2))) =
      some (rs.map Prod.snd) := by
  induction rs with
  | nil => rfl
  | cons q rs ih =>
      rcases q with ⟨m, c⟩
      simp only [List.map_cons, semChalsZ, ih, Option.map_some]

#print axioms semChalsZ_of_pairs

theorem semChalsZ_some_structure
    (rounds : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
    (h : semChalsZ rounds = some cs) :
    ∃ rs : List (SemMsgZ K × K),
      rounds = rs.map (fun q => (Msg.semantic q.1, Chal.semantic q.2)) ∧
      cs = rs.map Prod.snd := by
  induction rounds generalizing cs with
  | nil =>
      have hc : cs = [] := Option.some.inj h.symm
      exact ⟨[], rfl, hc⟩
  | cons q rounds ih =>
      rcases q with ⟨m, c⟩
      cases m <;> cases c <;> simp [semChalsZ] at h
      rename_i sm c
      obtain ⟨tail, htail, rfl⟩ := h
      obtain ⟨rs, hrs, hcs⟩ := ih tail htail
      exact ⟨(sm, c) :: rs, by simp only [List.map_cons, hrs],
        by simp only [List.map_cons, hcs]⟩

#print axioms semChalsZ_some_structure

theorem semChalsZ_length
    (rounds : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
    (h : semChalsZ rounds = some cs) : cs.length = rounds.length := by
  obtain ⟨rs, rfl, rfl⟩ := semChalsZ_some_structure rounds cs h
  simp only [List.length_map]

#print axioms semChalsZ_length

theorem semChalsZ_take
    (rounds : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
    (h : semChalsZ rounds = some cs) (n : Nat) :
    semChalsZ (rounds.take n) = some (cs.take n) := by
  obtain ⟨rs, rfl, rfl⟩ := semChalsZ_some_structure rounds cs h
  simp only [← List.map_take]
  exact semChalsZ_of_pairs (rs.take n)

#print axioms semChalsZ_take

theorem semChalsZ_getElem
    (rounds : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
    (h : semChalsZ rounds = some cs) (i : Fin rounds.length) :
    ∃ sm : SemMsgZ K, rounds[i.val] =
      (Msg.semantic sm, Chal.semantic (cs[i.val]'(by
        have hlen := semChalsZ_length rounds cs h
        omega))) := by
  obtain ⟨rs, rfl, rfl⟩ := semChalsZ_some_structure rounds cs h
  have hi : i.val < rs.length := by simpa only [List.length_map] using i.isLt
  refine ⟨(rs[i.val]'hi).1, ?_⟩
  simp only [List.getElem_map]

#print axioms semChalsZ_getElem

def openingPairsZ (os : List (R0FS.Msg K × R0FS.Chal K)) :
    List (Msg K K (SemMsgZ K) × Chal K K) :=
  os.map (fun q => (Msg.opening q.1, Chal.opening q.2))

#print axioms openingPairsZ

theorem openingRoundsZ_pairs (os : List (R0FS.Msg K × R0FS.Chal K)) :
    openingRoundsZ (openingPairsZ os) = some os := by
  induction os with
  | nil => rfl
  | cons q os ih =>
      rcases q with ⟨m, c⟩
      simp only [openingPairsZ, List.map_cons, openingRoundsZ] at ih ⊢
      rw [ih]
      rfl

#print axioms openingRoundsZ_pairs

theorem openingRoundsZ_some
    (rounds : List (Msg K K (SemMsgZ K) × Chal K K))
    (os : List (R0FS.Msg K × R0FS.Chal K))
    (h : openingRoundsZ rounds = some os) : rounds = openingPairsZ os := by
  induction rounds generalizing os with
  | nil =>
      have hos : os = [] := Option.some.inj h.symm
      subst os
      rfl
  | cons q rounds ih =>
      rcases q with ⟨m, c⟩
      cases m <;> cases c <;> simp [openingRoundsZ] at h
      rename_i om oc
      obtain ⟨tail, htail, rfl⟩ := h
      have ht := ih tail htail
      simpa only [openingPairsZ, List.map_cons] using
        congrArg (List.cons (Msg.opening om, Chal.opening oc)) ht

#print axioms openingRoundsZ_some

theorem semChalsZ_base (rs : List (MsgZ K × ChalZ K)) :
    semChals (baseRoundsZ rs) = semChalsZ rs := by
  induction rs with
  | nil => rfl
  | cons q rs ih =>
      rcases q with ⟨m,c⟩
      simp only [baseRoundsZ, unmaskMsg] at ih
      cases m <;> cases c <;> simp only [baseRoundsZ, List.map_cons, unmaskMsg,
        semChals, semChalsZ, ih]

theorem c2OfZ_take (rs : List (MsgZ K × ChalZ K)) (n : Nat) (hn : 2 < n) :
    c2OfZ (rs.take n) = c2OfZ rs := by
  unfold c2OfZ baseRoundsZ
  rw [List.map_take]
  exact R0P.SemD3Glue.c2Of_take _ n hn

theorem claimOf_take (rs : List (MsgZ K × ChalZ K)) (n : Nat) (hn : 14 < n) :
    claimOf (rs.take n) = claimOf rs := by
  simp only [claimOf, List.getElem?_take_of_lt hn]

def semPolysZ (rs : List (MsgZ K × ChalZ K)) : Option (Fin 10 → K[X]) :=
  if h : rs.length = 25 then
    let get : Fin 10 → Option K[X] := fun j =>
      match (rs[15 + j.val]'(by omega)).1 with
      | .semantic (.base (.roundPoly p)) => some p
      | _ => none
    if hall : ∀ j, (get j).isSome then some (fun j => (get j).get (hall j)) else none
  else none

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def openingViewZ {Sfield : Fin 29 → Subfield K} (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K)) :
    Option (FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)) :=
  match P.rounds.splitAt 25 with
  | (sem, (.beforeZ0 y, .circle z0) :: (.beforeZ1 _, .circle z1) :: opening) =>
    match semChalsZ sem, c2OfZ sem, openingRoundsZ opening with
    | some cs, some (hw, gw), some os =>
      if h : cs.length = 25 ∧ c2Base Sfield hw gw ∧ z0 ≠ z1 ∧ ¬ BaseRational z0 ∧
          ¬ BaseRational z1 then
        some ⟨openingStmt P.statement hw gw h.2.1
          (fun j => cs[15 + j.val]'(by omega)) y z0 z1 h.2.2.1 h.2.2.2.1 h.2.2.2.2, os⟩
      else Option.none
    | _, _, _ => Option.none
  | _ => Option.none

omit [Fintype K] in
theorem openingViewZ_of_parsed {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield)
    (sem : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
    (hsem : sem.length = 25) (hcs : cs.length = 25)
    (hparse : semChalsZ sem = some cs)
    (hw gw : InitialWord K) (hc2 : c2OfZ sem = some (hw, gw))
    (hb : c2Base Sfield hw gw)
    (y : Fin 3 → Fin 29 → K) (y₀ : Fin 29 → K) (z₀ z₁ : Point K)
    (hne : z₀ ≠ z₁) (h₀ : ¬ BaseRational z₀) (h₁ : ¬ BaseRational z₁)
    (os : List (R0FS.Msg K × R0FS.Chal K)) :
    openingViewZ ⟨x, sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairsZ os)⟩ =
      some ⟨openingStmt x hw gw hb (fun j => cs[15 + j.val]'(by omega))
        y z₀ z₁ hne h₀ h₁, os⟩ := by
  unfold openingViewZ
  rw [List.splitAt_eq]
  have htake : (sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairsZ os)).take 25 = sem := by
    rw [← hsem]
    exact List.take_left
  have hdrop : (sem ++
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairsZ os)).drop 25 =
      ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairsZ os) := by
    rw [← hsem]
    exact List.drop_left
  rw [htake, hdrop]
  simp only [hparse, hc2, openingRoundsZ_pairs]
  rw [dif_pos ⟨hcs, hb, hne, h₀, h₁⟩]

#print axioms openingViewZ_of_parsed

omit [Fintype K] in
theorem openingViewZ_some_structure {Sfield : Fin 29 → Subfield K}
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingViewZ P = some Q) :
    ∃ (sem : List (Msg K K (SemMsgZ K) × Chal K K)) (cs : List K)
      (hw gw : InitialWord K) (y : Fin 3 → Fin 29 → K) (y₀ : Fin 29 → K)
      (z₀ z₁ : Point K) (hcs : cs.length = 25) (hb : c2Base Sfield hw gw)
      (hne : z₀ ≠ z₁) (h₀ : ¬ BaseRational z₀) (h₁ : ¬ BaseRational z₁)
      (os : List (R0FS.Msg K × R0FS.Chal K)),
      sem.length = 25 ∧ semChalsZ sem = some cs ∧ c2OfZ sem = some (hw, gw) ∧
      P.rounds = sem ++
        ((Msg.beforeZ0 y, Chal.circle z₀) :: (Msg.beforeZ1 y₀, Chal.circle z₁) :: openingPairsZ os) ∧
      Q = ⟨openingStmt P.statement hw gw hb (fun j => cs[15 + j.val]'(by omega))
        y z₀ z₁ hne h₀ h₁, os⟩ := by
  cases hsplit : P.rounds.splitAt 25 with
  | mk sem suffix =>
      cases suffix with
      | nil =>
          simp only [openingViewZ, hsplit] at hview
          cases hview
      | cons first suffix =>
          rcases first with ⟨m₀, c₀⟩
          cases m₀ <;> cases c₀ <;> simp only [openingViewZ, hsplit] at hview
          all_goals try contradiction
          rename_i y z₀
          cases suffix with
          | nil => simp at hview
          | cons second opening =>
              rcases second with ⟨m₁, c₁⟩
              cases m₁ <;> cases c₁ <;> simp only at hview
              all_goals try contradiction
              rename_i y₀ z₁
              cases hparse : semChalsZ sem with
              | none => simp only [hparse] at hview; contradiction
              | some cs =>
                  cases hc2 : c2OfZ sem with
                  | none => simp only [hparse, hc2] at hview; contradiction
                  | some words =>
                      rcases words with ⟨hw, gw⟩
                      cases hopen : openingRoundsZ opening with
                      | none => simp only [hparse, hc2, hopen] at hview; contradiction
                      | some os =>
                          simp only [hparse, hc2, hopen] at hview
                          split at hview
                          · rename_i hvalid
                            have hQ := Option.some.inj hview
                            have hlen : sem.length = 25 :=
                              (semChalsZ_length sem cs hparse).symm.trans hvalid.1
                            have hrounds : P.rounds = sem ++
                                ((Msg.beforeZ0 y, Chal.circle z₀) ::
                                  (Msg.beforeZ1 y₀, Chal.circle z₁) :: opening) := by
                              have hs := congrArg (fun q => q.1 ++ q.2) hsplit
                              simpa only [List.splitAt_eq, List.take_append_drop] using hs
                            refine ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hvalid.1,
                              hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1, hvalid.2.2.2.2,
                              os, hlen, hparse, hc2, ?_, hQ.symm⟩
                            rw [openingRoundsZ_some opening os hopen] at hrounds
                            exact hrounds
                          · contradiction

#print axioms openingViewZ_some_structure

theorem hitFromZ_suffix {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsgZ K) W Sfield) (x : X) :
    ∀ (front tail prev : List (Msg K K (SemMsgZ K) × Chal K K)),
      hitFrom s x (prev ++ front) tail → hitFrom s x prev (front ++ tail) := by
  intro front
  induction front with
  | nil =>
      intro tail prev h
      simpa only [List.append_nil, List.nil_append] using h
  | cons q front ih =>
      intro tail prev h
      rcases q with ⟨m, c⟩
      apply Or.inr
      apply ih tail (prev ++ [(m, c)])
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

#print axioms hitFromZ_suffix

theorem openingZ_goodFrom_hitFrom {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsgZ K) W Sfield) (x : X)
    (base : List (Msg K K (SemMsgZ K) × Chal K K)) (stmt : R0FS.Stmt K Sfield)
    (hbase : base.length = s.semanticRounds + 2)
    (hview : ∀ prev, s.openingView ⟨x, base ++ openingPairsZ prev⟩ = some ⟨stmt, prev⟩) :
    ∀ (rest prev : List (R0FS.Msg K × R0FS.Chal K)),
      R0FS.goodFrom stmt prev rest →
        hitFrom s x (base ++ openingPairsZ prev) (openingPairsZ rest) := by
  intro rest
  induction rest with
  | nil =>
      intro prev h
      exact False.elim h
  | cons q rest ih =>
      intro prev h
      rcases q with ⟨m, c⟩
      change R0FS.roundBad stmt prev m c ∨
        R0FS.goodFrom stmt (prev ++ [(m, c)]) rest at h
      change roundBad s ⟨x, base ++ openingPairsZ prev⟩ (.opening m) (.opening c) ∨
        hitFrom s x ((base ++ openingPairsZ prev) ++ [(.opening m, .opening c)])
          (openingPairsZ rest)
      rcases h with hbad | htail
      · left
        apply Or.inr
        apply Or.inr
        apply Or.inr
        refine ⟨⟨stmt, prev⟩, m, c, hview prev, rfl, rfl, ?_, hbad⟩
        simp only [FS.Prefix.round, List.length_append, openingPairsZ, List.length_map, hbase]
      · right
        have ht := ih (prev ++ [(m, c)]) htail
        simpa only [openingPairsZ, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc] using ht

#print axioms openingZ_goodFrom_hitFrom

theorem openingZ_good_hitFrom {W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) (TypedContext K Sfield) (SemMsgZ K) W Sfield)
    (hsview : s.openingView = openingViewZ) (hsrounds : s.semanticRounds = 25)
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingViewZ P = some Q) (hgood : R0FS.good Q.statement Q.rounds) :
    hitFrom s P.statement [] P.rounds := by
  obtain ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hcs, hb, hne, h₀, h₁, os,
    hsem, hparse, hc2, hrounds, hQ⟩ := openingViewZ_some_structure P Q hview
  subst Q
  let base := sem ++ [(Msg.beforeZ0 y, Chal.circle z₀), (Msg.beforeZ1 y₀, Chal.circle z₁)]
  let stmt := openingStmt P.statement hw gw hb (fun j => cs[15 + j.val]'(by omega))
    y z₀ z₁ hne h₀ h₁
  have hbase : base.length = s.semanticRounds + 2 := by
    simp only [base, List.length_append, List.length_cons, List.length_nil, hsem, hsrounds]
  have hprefix : ∀ prev, s.openingView ⟨P.statement, base ++ openingPairsZ prev⟩ =
      some ⟨stmt, prev⟩ := by
    intro prev
    rw [hsview]
    simpa only [base, stmt, List.append_assoc, List.cons_append, List.nil_append] using
      openingViewZ_of_parsed P.statement sem cs hsem hcs hparse hw gw hc2 hb
        y y₀ z₀ z₁ hne h₀ h₁ prev
  have htail := openingZ_goodFrom_hitFrom s P.statement base stmt hbase hprefix os [] hgood
  have htail' : hitFrom s P.statement ([] ++ base) (openingPairsZ os) := by
    simpa only [openingPairsZ, List.map_nil, List.append_nil, List.nil_append] using htail
  have hall := hitFromZ_suffix s P.statement base (openingPairsZ os) [] htail'
  rw [hrounds]
  simpa only [base, List.append_assoc, List.cons_append, List.nil_append] using hall

#print axioms openingZ_good_hitFrom


/-- No degree guard occurs on the eta claim. Only the ten alpha messages
are polynomial messages whose degrees the verifier checks. -/
def decisionZ {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (maskPoly : (Fin 10 → K) → K) (B : PackBasis F)
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K)) (m : MsgZ K) : Bool :=
  if ∃ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (cs : List K) (hcs : cs.length = 25) (polys : Fin 10 → K[X]) (claim : K) (om : R0FS.Msg K),
    openingViewZ P = some Q ∧ semChalsZ (P.rounds.take 25) = some cs ∧
    semPolysZ (P.rounds.take 25) = some polys ∧ claimOf P.rounds = some claim ∧
    sumcheckChecksZ maskPoly P.statement.pub B
      (fun j => cs[j.val]'(by omega)) (cs[14]'(by omega)) claim
      (fun j => cs[15 + j.val]'(by omega)) polys Q.statement.pointClaims ∧
    m = .opening om ∧ R0FS.decision Q om = true ∧ cardOK Q = true
  then true else false

#print axioms semChalsZ_base
#print axioms c2OfZ_take
#print axioms claimOf_take
#print axioms semPolysZ
#print axioms openingViewZ
#print axioms decisionZ
end
end R0P.Mask
