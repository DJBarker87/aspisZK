import R1Z.LensR1

/-! R1 games (zf1/DESIGN-R1-GAMES §2): the byte layout of one attempt's
Fiat-Shamir transcript, 115 oracle reads (SOURCE: r1_wire.rs
SemanticTranscript, transcript.rs Transcript, verifier.rs Prepared::new,
r0_transcript.rs queries_from_pairs; variant S2, two folds, 33 rows):

* `init` = H(DOMAIN ‖ 0 ‖ le32 |pub| ‖ pub ‖ c1_root);
* rows 0..26: `absS i` = H(state ‖ 0 ‖ 0xa0+i ‖ framed_i), `sqS i` =
  H(absorbed ‖ 1) (challenge block), `advS i` = H(absorbed ‖ 2) (next state);
* `reseed` = H(DOMAIN2 ‖ variant ‖ state_26);
* rows 27..30: `absO i` = H(state ‖ 0 ‖ 0xa0+27+i ‖ le32 |payload| ‖ payload),
  `sqO i`, `advO i`;
* row 31: `absQ` (final message), eight pairs `qb k` = H(st_k ‖ 1),
  `qa k` = H(st_k ‖ 2) with st_0 = absorbed, st_{k+1} = answer of `qa k`;
* row 32: `absR` = H(a_{k*} ‖ 0 ‖ 0xc0 ‖ le32 0), `sqR`, `advR`, where k* is
  the QueryScan completion index (a function of the `qb` answers only).

Every address carries one DESIGNATED FIELD (`fc`): a 32-byte coordinate at
offset 0 (or trailing, for `init` and `reseed`) that is the C1 root, the
answer of an earlier read, or (for `absR`) the answer of `qa k*` (`sel`).
The rest of the address (`Rest`) is public data and the prover's messages.
A record `Rec` collects the coordinates; `setC` moves one of them.

PROVED here: `card_TRead` (115 reads; 40 squeeze blocks), the field readers
(`extract_addrWith`), invariance of every address under every coordinate it
does not read (`addr_setC_of_not_dep`), and the pair table `table`: two
distinct reads either have a coordinate one of them does not read, or their
addresses differ for every record (suffix byte 1 vs 2; length 38 vs 33).
Lifted to any space with per-attempt lenses (`TranscriptFrame`), this gives
`PairFresh` for every pair of transcript positions of all attempts and
`HitFresh` for every transcript position whose charging event and adversary
read are lens-invariant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.TranscriptR1
open R0Z.FsAbortBounds R1Z.LensR1
attribute [local instance] Classical.propDecidable

/-! ### The 115 reads -/

inductive TRead
  | init
  | absS (i : Fin 27) | sqS (i : Fin 27) | advS (i : Fin 27)
  | reseed
  | absO (i : Fin 4) | sqO (i : Fin 4) | advO (i : Fin 4)
  | absQ
  | qb (k : Fin 8) | qa (k : Fin 8)
  | absR | sqR | advR
  deriving DecidableEq

abbrev TSum := Unit ⊕ Fin 27 ⊕ Fin 27 ⊕ Fin 27 ⊕ Unit ⊕ Fin 4 ⊕ Fin 4 ⊕ Fin 4 ⊕ Unit ⊕ Fin 8 ⊕ Fin 8 ⊕ Unit ⊕ Unit ⊕ Unit

def TRead.toSum : TRead → TSum
  | .init => .inl ()
  | .absS x => .inr (.inl x)
  | .sqS x => .inr (.inr (.inl x))
  | .advS x => .inr (.inr (.inr (.inl x)))
  | .reseed => .inr (.inr (.inr (.inr (.inl ()))))
  | .absO x => .inr (.inr (.inr (.inr (.inr (.inl x)))))
  | .sqO x => .inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))
  | .advO x => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))))
  | .absQ => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))
  | .qb x => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))))))
  | .qa x => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))))))
  | .absR => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))))
  | .sqR => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))))
  | .advR => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (())))))))))))))

def TRead.ofSum : TSum → TRead
  | .inl _ => .init
  | .inr (.inl x) => .absS x
  | .inr (.inr (.inl x)) => .sqS x
  | .inr (.inr (.inr (.inl x))) => .advS x
  | .inr (.inr (.inr (.inr (.inl _)))) => .reseed
  | .inr (.inr (.inr (.inr (.inr (.inl x))))) => .absO x
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))) => .sqO x
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))) => .advO x
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))))) => .absQ
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))))) => .qb x
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))))))) => .qa x
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))))))) => .absR
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))))))))) => .sqR
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (_))))))))))))) => .advR

def TRead.equivSum : TRead ≃ TSum where
  toFun := TRead.toSum
  invFun := TRead.ofSum
  left_inv j := by cases j <;> rfl
  right_inv x := by
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rfl

instance : Fintype TRead := Fintype.ofEquiv TSum TRead.equivSum.symm

/-- The read count of one attempt's transcript (design §2.1). -/
theorem card_TRead : Fintype.card TRead = 115 := by
  rw [Fintype.card_congr TRead.equivSum]
  simp [TSum, Fintype.card_sum]

/-- Squeeze reads: their answers are the challenge blocks (40 of them). -/
def IsSq : TRead → Prop
  | .sqS _ => True
  | .sqO _ => True
  | .qb _ => True
  | .sqR => True
  | _ => False

/-- The verifier's (and honest prover's) read order. -/
def schedule : List TRead :=
  [.init] ++ (List.finRange 27).flatMap (fun i => [.absS i, .sqS i, .advS i]) ++ [.reseed] ++
    (List.finRange 4).flatMap (fun i => [.absO i, .sqO i, .advO i]) ++ [.absQ] ++
    (List.finRange 8).flatMap (fun k => [.qb k, .qa k]) ++ [.absR, .sqR, .advR]

theorem mem_schedule (j : TRead) : j ∈ schedule := by
  cases j <;> simp [schedule]

/-! ### Coordinates and designated fields -/

inductive Coord
  | root
  | sel
  | ans (j : TRead)
  deriving DecidableEq

def fc : TRead → Coord
  | .init => .root
  | .absS ⟨0, _⟩ => .ans .init
  | .absS ⟨i + 1, h⟩ => .ans (.advS ⟨i, by omega⟩)
  | .sqS i => .ans (.absS i)
  | .advS i => .ans (.absS i)
  | .reseed => .ans (.advS ⟨26, by omega⟩)
  | .absO ⟨0, _⟩ => .ans .reseed
  | .absO ⟨i + 1, h⟩ => .ans (.advO ⟨i, by omega⟩)
  | .sqO i => .ans (.absO i)
  | .advO i => .ans (.absO i)
  | .absQ => .ans (.advO ⟨3, by omega⟩)
  | .qb ⟨0, _⟩ => .ans .absQ
  | .qb ⟨k + 1, h⟩ => .ans (.qa ⟨k, by omega⟩)
  | .qa ⟨0, _⟩ => .ans .absQ
  | .qa ⟨k + 1, h⟩ => .ans (.qa ⟨k, by omega⟩)
  | .absR => .sel
  | .sqR => .ans .absR
  | .advR => .ans .absR

/-! ### Records and addresses -/

/-- Public data and the prover's messages of one attempt. -/
structure Rest where
  framed : Fin 27 → Bytes
  payload : Fin 4 → Bytes
  final : Bytes
  pubB : Bytes
  vtag : UInt8

/-- One attempt's coordinates: every read's answer, the C1 root, k*. -/
structure Rec where
  tr : TRead → Ans
  c1 : Ans
  kstar : Fin 8
  rest : Rest

def fieldVal : Coord → Rec → Ans
  | .root, ρ => ρ.c1
  | .sel, ρ => ρ.tr (.qa ρ.kstar)
  | .ans j, ρ => ρ.tr j

/-- "UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3" (r1_wire.rs DOMAIN, P3 build). -/
def semDomain : Bytes := "UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3".toUTF8.toList

/-- "UNPROVED:R1:PRIVATE-SALTED:P3" (transcript.rs Transcript::new, P3 build). -/
def openDomain : Bytes := "UNPROVED:R1:PRIVATE-SALTED:P3".toUTF8.toList

def le32 (n : ℕ) : Bytes :=
  [(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
    (n / 16777216 % 256).toUInt8]

/-- The address of read `j` with designated-field value `f`. -/
def addrWith : TRead → Ans → Rest → Bytes
  | .init, f, r => semDomain ++ [0] ++ le32 r.pubB.length ++ r.pubB ++ ans f
  | .absS i, f, r => ans f ++ ([0, 0xa0 + i.val.toUInt8] ++ r.framed i)
  | .sqS _, f, _ => ans f ++ [1]
  | .advS _, f, _ => ans f ++ [2]
  | .reseed, f, r => openDomain ++ [r.vtag] ++ ans f
  | .absO i, f, r =>
      ans f ++ ([0, 0xa0 + (27 + i.val).toUInt8] ++ le32 (r.payload i).length ++ r.payload i)
  | .sqO _, f, _ => ans f ++ [1]
  | .advO _, f, _ => ans f ++ [2]
  | .absQ, f, r => ans f ++ ([0, 0xa0 + 31] ++ le32 r.final.length ++ r.final)
  | .qb _, f, _ => ans f ++ [1]
  | .qa _, f, _ => ans f ++ [2]
  | .absR, f, _ => ans f ++ ([0, 0xa0 + 32] ++ le32 0)
  | .sqR, f, _ => ans f ++ [1]
  | .advR, f, _ => ans f ++ [2]

def addr (j : TRead) (ρ : Rec) : Bytes := addrWith j (fieldVal (fc j) ρ) ρ.rest

/-- The designated-field reader of read `j`. -/
def extract : TRead → Bytes → Ans
  | .init => trailing
  | .reseed => trailing
  | _ => fixed0

theorem extract_addrWith (j : TRead) (f : Ans) (r : Rest) : extract j (addrWith j f r) = f := by
  cases j <;> first | exact fixed0_ans_append _ _ | exact trailing_append_ans _ _

/-! ### Moving one coordinate -/

def setC : Coord → Rec → Ans → Rec
  | .root, ρ, u => { ρ with c1 := u }
  | .sel, ρ, u => { ρ with tr := Function.update ρ.tr (.qa ρ.kstar) u }
  | .ans j, ρ, u => { ρ with tr := Function.update ρ.tr j u }

theorem fieldVal_setC (c : Coord) (ρ : Rec) (u : Ans) : fieldVal c (setC c ρ u) = u := by
  cases c <;> simp [fieldVal, setC]

theorem rest_setC (c : Coord) (ρ : Rec) (u : Ans) : (setC c ρ u).rest = ρ.rest := by
  cases c <;> rfl

theorem kstar_setC (c : Coord) (ρ : Rec) (u : Ans) : (setC c ρ u).kstar = ρ.kstar := by
  cases c <;> rfl

theorem extract_addr_setC (j : TRead) (ρ : Rec) (u : Ans) :
    extract j (addr j (setC (fc j) ρ u)) = u := by
  unfold addr
  rw [rest_setC, fieldVal_setC]
  exact extract_addrWith _ _ _

/-- `c` reads `c'`: equal, or one is `sel` and the other a `qa` answer
(`sel` is the answer of `qa k*`). -/
def Dep (c c' : Coord) : Prop :=
  c = c' ∨ (c = .sel ∧ ∃ k, c' = .ans (.qa k)) ∨ (c' = .sel ∧ ∃ k, c = .ans (.qa k))

theorem fieldVal_setC_of_not_dep : ∀ (c c' : Coord) (ρ : Rec) (u : Ans), ¬ Dep c c' →
    fieldVal c (setC c' ρ u) = fieldVal c ρ
  | .root, .root, _, _, h => (h (Or.inl rfl)).elim
  | .root, .sel, _, _, _ => rfl
  | .root, .ans _, _, _, _ => rfl
  | .sel, .root, _, _, _ => rfl
  | .sel, .sel, _, _, h => (h (Or.inl rfl)).elim
  | .sel, .ans j, ρ, u, h => by
      have hj : TRead.qa ρ.kstar ≠ j := fun e => h (Or.inr (Or.inl ⟨rfl, ρ.kstar, by rw [e]⟩))
      show Function.update ρ.tr j u (.qa ρ.kstar) = ρ.tr (.qa ρ.kstar)
      exact Function.update_of_ne hj _ _
  | .ans _, .root, _, _, _ => rfl
  | .ans j, .sel, ρ, u, h => by
      have hj : j ≠ TRead.qa ρ.kstar := fun e => h (Or.inr (Or.inr ⟨rfl, ρ.kstar, by rw [e]⟩))
      show Function.update ρ.tr (.qa ρ.kstar) u j = ρ.tr j
      exact Function.update_of_ne hj _ _
  | .ans j, .ans j', ρ, u, h => by
      have hj : j ≠ j' := fun e => h (Or.inl (by rw [e]))
      show Function.update ρ.tr j' u j = ρ.tr j
      exact Function.update_of_ne hj _ _

theorem addr_setC_of_not_dep (j : TRead) (c : Coord) (ρ : Rec) (u : Ans)
    (h : ¬ Dep (fc j) c) : addr j (setC c ρ u) = addr j ρ := by
  unfold addr
  rw [rest_setC, fieldVal_setC_of_not_dep _ _ _ _ h]

/-! ### The pair table -/

def rep : TRead → TRead
  | .advS i => .sqS i
  | .advO i => .sqO i
  | .qa k => .qb k
  | .advR => .sqR
  | j => j

def back : Coord → TRead
  | .root => .init
  | .sel => .absR
  | .ans .init => .absS 0
  | .ans (.absS i) => .sqS i
  | .ans (.advS i) => if h : i.val + 1 < 27 then .absS ⟨i.val + 1, h⟩ else .reseed
  | .ans .reseed => .absO 0
  | .ans (.absO i) => .sqO i
  | .ans (.advO i) => if h : i.val + 1 < 4 then .absO ⟨i.val + 1, h⟩ else .absQ
  | .ans .absQ => .qb 0
  | .ans (.qa k) => if h : k.val + 1 < 8 then .qb ⟨k.val + 1, h⟩ else .init
  | .ans .absR => .sqR
  | .ans _ => .init

theorem back_fc : ∀ j : TRead, back (fc j) = rep j
  | .init => rfl
  | .absS ⟨0, _⟩ => rfl
  | .absS ⟨i + 1, h⟩ => by
      show (if h' : i + 1 < 27 then TRead.absS ⟨i + 1, h'⟩ else TRead.reseed) = TRead.absS ⟨i + 1, h⟩
      rw [dif_pos h]
  | .sqS _ => rfl
  | .advS _ => rfl
  | .reseed => by
      show (if h' : 26 + 1 < 27 then TRead.absS ⟨26 + 1, h'⟩ else TRead.reseed) = TRead.reseed
      rw [dif_neg (by omega)]
  | .absO ⟨0, _⟩ => rfl
  | .absO ⟨i + 1, h⟩ => by
      show (if h' : i + 1 < 4 then TRead.absO ⟨i + 1, h'⟩ else TRead.absQ) = TRead.absO ⟨i + 1, h⟩
      rw [dif_pos h]
  | .sqO _ => rfl
  | .advO _ => rfl
  | .absQ => by
      show (if h' : 3 + 1 < 4 then TRead.absO ⟨3 + 1, h'⟩ else TRead.absQ) = TRead.absQ
      rw [dif_neg (by omega)]
  | .qb ⟨0, _⟩ => rfl
  | .qb ⟨k + 1, h⟩ => by
      show (if h' : k + 1 < 8 then TRead.qb ⟨k + 1, h'⟩ else TRead.init) = TRead.qb ⟨k + 1, h⟩
      rw [dif_pos h]
  | .qa ⟨0, _⟩ => rfl
  | .qa ⟨k + 1, h⟩ => by
      show (if h' : k + 1 < 8 then TRead.qb ⟨k + 1, h'⟩ else TRead.init) = TRead.qb ⟨k + 1, h⟩
      rw [dif_pos h]
  | .absR => rfl
  | .sqR => rfl
  | .advR => rfl

/-- Sibling squeeze/advance reads of one state. -/
def Sib (j j' : TRead) : Prop :=
  (∃ i, j = .sqS i ∧ j' = .advS i) ∨ (∃ i, j = .advS i ∧ j' = .sqS i) ∨
  (∃ i, j = .sqO i ∧ j' = .advO i) ∨ (∃ i, j = .advO i ∧ j' = .sqO i) ∨
  (∃ k, j = .qb k ∧ j' = .qa k) ∨ (∃ k, j = .qa k ∧ j' = .qb k) ∨
  (j = .sqR ∧ j' = .advR) ∨ (j = .advR ∧ j' = .sqR)

theorem rep_cases (j j' : TRead) (h : rep j = rep j') : j = j' ∨ Sib j j' := by
  cases j <;> cases j' <;> simp_all [rep, Sib]

theorem ne_suffix (f f' : Ans) : ans f ++ [1] ≠ ans f' ++ [2] := by
  intro h
  have h2 := (List.append_inj h (by rw [length_ans, length_ans])).2
  exact absurd h2 (by decide)

theorem sib_addr_ne (j j' : TRead) (h : Sib j j') (f f' : Ans) (r r' : Rest) :
    addrWith j f r ≠ addrWith j' f' r' := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ |
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact ne_suffix f f'
    | exact fun e => ne_suffix f' f e.symm

theorem fc_eq_sel (j : TRead) (h : fc j = .sel) : j = .absR := by
  have hb := back_fc j
  rw [h] at hb
  rcases rep_cases j .absR hb.symm with e | e
  · exact e
  · simp [Sib] at e

theorem fc_eq_qa (j : TRead) (k : Fin 8) (h : fc j = .ans (.qa k)) :
    (∃ m, j = .qb m) ∨ (∃ m, j = .qa m) := by
  have hb := back_fc j
  rw [h] at hb
  by_cases hk : k.val + 1 < 8
  · have hb' : rep j = rep (.qb ⟨k.val + 1, hk⟩) := by
      rw [← hb]
      show (if h' : k.val + 1 < 8 then TRead.qb ⟨k.val + 1, h'⟩ else TRead.init) =
        TRead.qb ⟨k.val + 1, hk⟩
      rw [dif_pos hk]
    rcases rep_cases j _ hb' with e | e
    · exact Or.inl ⟨_, e⟩
    · simp [Sib] at e
      exact Or.inr ⟨_, e⟩
  · have hb' : rep j = rep .init := by
      rw [← hb]
      show (if h' : k.val + 1 < 8 then TRead.qb ⟨k.val + 1, h'⟩ else TRead.init) = TRead.init
      rw [dif_neg hk]
    rcases rep_cases j _ hb' with e | e
    · subst e
      simp [fc] at h
    · simp [Sib] at e

theorem len_absR (f : Ans) (r : Rest) : (addrWith .absR f r).length = 38 := by
  simp [addrWith, length_ans, le32]

theorem len_qbqa (j : TRead) (hj : (∃ m, j = .qb m) ∨ (∃ m, j = .qa m)) (f : Ans) (r : Rest) :
    (addrWith j f r).length = 33 := by
  rcases hj with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> simp [addrWith, length_ans]

/-- The pair table: two distinct reads of one attempt either have a
designated field that the other does not read, or never share an address. -/
theorem table (j j' : TRead) (hne : j ≠ j') :
    ¬ Dep (fc j) (fc j') ∨ ∀ ρ : Rec, addr j ρ ≠ addr j' ρ := by
  by_cases hd : Dep (fc j) (fc j')
  · right
    intro ρ
    rcases hd with he | ⟨hs, k, hk⟩ | ⟨hs, k, hk⟩
    · have hr : rep j = rep j' := by rw [← back_fc, ← back_fc, he]
      rcases rep_cases j j' hr with e | e
      · exact absurd e hne
      · exact sib_addr_ne j j' e _ _ _ _
    · have h1 := fc_eq_sel j hs
      subst h1
      intro e
      have hl := congrArg List.length e
      unfold addr at hl
      rw [len_absR, len_qbqa j' (fc_eq_qa j' k hk)] at hl
      omega
    · have h1 := fc_eq_sel j' hs
      subst h1
      intro e
      have hl := congrArg List.length e
      unfold addr at hl
      rw [len_absR, len_qbqa j (fc_eq_qa j k hk)] at hl
      omega
  · exact Or.inl hd

/-- No designated field is a squeeze answer: squeeze answers feed the
decoders only (design §2.2). -/
theorem fc_not_sq (j j' : TRead) (h : fc j = .ans j') : ¬ IsSq j' := by
  intro hs
  have hb := back_fc j
  rw [h] at hb
  have hi : back (.ans j') = .init := by
    cases j' <;> first | rfl | exact False.elim hs
  rw [hi] at hb
  rcases rep_cases j .init hb.symm with e | e
  · subst e
    simp [fc] at h
  · simp [Sib] at e

/-- A chain coordinate: the C1 root, `sel`, or the answer of a non-squeeze
read.  Every designated field is one (`chain_fc`); moving a chain coordinate
leaves the challenges and the prover's messages unchanged. -/
def ChainC (c : Coord) : Prop := ∀ j, c = .ans j → ¬ IsSq j

theorem chain_fc (j : TRead) : ChainC (fc j) := fun j' h => fc_not_sq j j' h

/-! ### Lifting to a space of attempts -/

/-- Per-attempt records on a finite space `S`, with a lawful lens for every
chain coordinate of every attempt: moving chain coordinate `c` of attempt `k`
moves that coordinate of `k`'s record and leaves every other attempt's record
alone. -/
structure TranscriptFrame (S : Type) (N : ℕ) where
  att : Fin N → S → Rec
  lens : Fin N → Coord → Lens S Ans
  rec_same : ∀ k c s u, ChainC c → att k ((lens k c).set s u) = setC c (att k s) u
  rec_other : ∀ k k' c s u, k' ≠ k → att k' ((lens k c).set s u) = att k' s

variable {S : Type} [Fintype S] {N : ℕ}

def taddr (Fr : TranscriptFrame S N) (k : Fin N) (j : TRead) (s : S) : Bytes :=
  addr j (Fr.att k s)

theorem taddr_extract (Fr : TranscriptFrame S N) (k : Fin N) (j : TRead) (s : S) (u : Ans) :
    extract j (taddr Fr k j ((Fr.lens k (fc j)).set s u)) = u := by
  unfold taddr
  rw [Fr.rec_same _ _ _ _ (chain_fc j)]
  exact extract_addr_setC _ _ _

/-- `PairFresh` for every pair of distinct transcript positions, over all
attempts, with designated fields of `2^256 ≥ 2^255` values. -/
theorem pairFresh_transcript (Fr : TranscriptFrame S N) (p p' : Fin N × TRead) (hne : p ≠ p') :
    PairFresh (taddr Fr p.1 p.2) (taddr Fr p'.1 p'.2) (2 ^ 255) ∨
      PairFresh (taddr Fr p'.1 p'.2) (taddr Fr p.1 p.2) (2 ^ 255) := by
  obtain ⟨k, j⟩ := p
  obtain ⟨k', j'⟩ := p'
  by_cases hk : k = k'
  · subst hk
    have hj : j ≠ j' := fun e => hne (by rw [e])
    rcases table j j' hj with hd | hd
    · refine Or.inl (pairFresh_of_lens (Fr.lens k (fc j')) _ _ (extract j') _
        umin_le_card_ans ?_ (taddr_extract Fr k j'))
      intro s u
      unfold taddr
      rw [Fr.rec_same _ _ _ _ (chain_fc j')]
      exact addr_setC_of_not_dep j _ _ _ hd
    · exact Or.inl (pairFresh_of_ne _ _ _ (fun s => hd (Fr.att k s)))
  · refine Or.inl (pairFresh_of_lens (Fr.lens k' (fc j')) _ _ (extract j') _
      umin_le_card_ans ?_ (taddr_extract Fr k' j'))
    intro s u
    unfold taddr
    rw [Fr.rec_other k' k _ _ _ hk]

/-- `HitFresh` for a transcript position whose charging event and adversary
read do not move with the position's designated field. -/
theorem hitFresh_transcript (Fr : TranscriptFrame S N) (k : Fin N) (j : TRead)
    (D : S → Prop) (qa : S → Bytes)
    (hD : ∀ s u, D s → D ((Fr.lens k (fc j)).set s u))
    (hq : ∀ s u, D s → qa ((Fr.lens k (fc j)).set s u) = qa s) :
    HitFresh D qa (taddr Fr k j) (2 ^ 255) :=
  hitFresh_of_lens _ D qa _ (extract j) _ umin_le_card_ans hD hq (taddr_extract Fr k j)

/-- Transcript positions of `N` attempts: `N · 115`. -/
theorem card_positions : Fintype.card (Fin N × TRead) = N * 115 := by
  rw [Fintype.card_prod, Fintype.card_fin, card_TRead]

#print axioms TRead.equivSum
#print axioms card_TRead
#print axioms mem_schedule
#print axioms fc_not_sq
#print axioms chain_fc
#print axioms extract_addrWith
#print axioms fieldVal_setC
#print axioms extract_addr_setC
#print axioms fieldVal_setC_of_not_dep
#print axioms addr_setC_of_not_dep
#print axioms back_fc
#print axioms rep_cases
#print axioms sib_addr_ne
#print axioms fc_eq_sel
#print axioms fc_eq_qa
#print axioms table
#print axioms taddr_extract
#print axioms pairFresh_transcript
#print axioms hitFresh_transcript
#print axioms card_positions
end R1Z.TranscriptR1
