import NPH_R22JoinSM3F
import NPH_R22JoinSM2
import RPt_FIp_SemanticValues
import RPv_FJa_ClaimsCanonical
import RPv_FJn_BeginCanonical
import RPz7_SemanticRoundAlphaSelectedCanonical
import RPu_FIq_S_RawActualDecodeKMainAdapter
import NLU_TerminalCanonical
import LIB_VPublicAsset
import ExtractedPublicPreparationSuccess
import RPz7_S1SemanticRootCopyV1
import RPz7_ClaimsUnrolledFinish
import RPv_IDa_Deployed

/-! NPH_ (R22, SM step 3): producers for every SM boundary call of the deployed tx1 semantic finish,
composed through NPH_R22JoinSM3.finish_congr / verify_congr.
Deployed boundaries `Bd std r` = S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std
(IDa_Deployed.boundaries r)) (the op9 slot's finish boundaries, NOC_Op9Slot.slot/NOC_FinishSource.Bi).
Its mask/add/mul slots are FIp_SemanticArithmetic.mask/add/mul (`deployed_slots`, rfl), so the
deployed record is definitionally FIp_SemanticArithmetic.install of itself (`deployed_install`).
Guarded record `Bg std r`: the same record whose mask runs FIp mask only when every c1, mask-only
and point cell and g are canonical, and whose add/mul run FIp add/mul only on canonical operands
(otherwise fail).
Producers (closure theorems, applied at the SAME successful calls):
- alpha: SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical (rounds, any R);
- claims: ClaimsUnrolledFinish.claims_value + FJa_ClaimsCanonical.value (every claims cell);
- a, a1: NPH_R22JoinSM3.fromFn_mem with closure9_mem/closure5_mem (cells of claims[0]);
- q = claims[0][27]: membership in claims;
- mask output: NPH_R22JoinSM2.FIp_mask_site (canonical), the mul output and the first sum:
  FIp_SemanticValues.mul/add (canonical on canonical operands);
- val3[28]: RawActualDecodeKMainAdapter.decodeMain_success_members_canonical;
- eta and the terminal challenge inputs: FJn_BeginCanonical.value (successful begin in verify);
- val2 (the Ok terminal output): NLU_Terminal.source under NLU_Terminal.InputDomain, whose
  asset half is LIB_VPublicAsset.bytes_asset at the public_bytes of the SAME successful
  public transcript (PreparationSuccess.public_transcript_success), and whose digest half is
  the theorem premise `LIB_VPublicDomain.publicDigestDom pub` (producer at 345:
  NOM_TerminalDomain.validated_digest; its tie to the op9 public is NOT composed here).
`deployed_verify_guarded`: for every public with the digest domain, the verify prefix over the
deployed finish equals the same verify over the guarded finish. Site lemmas
`guarded_mask_site`/`guarded_add_site`/`guarded_mul_site`: wherever the guarded record runs a
kernel, its arguments are canonical and the kernel is ok with canonical (mask) or W (add/mul)
output (NPH_R22JoinSM2.FIp_mask_site, NPH_R22JoinSM.FIp_add_W/FIp_mul_W). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM4
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1.NPH_R22JoinSM3 (Q Claims bind_congr_ok idx_mem fromFn_mem closure9_mem closure5_mem
  finish_congr verify_congr)

abbrev Canon (x : Q) : Prop := AspisR1.FIp_SemanticValues.Canon x
abbrev AllC {n : Usize} (a : Array Q n) : Prop := ∀ x ∈ a.val, Canon x

def Bd (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation) : FinishModel.Boundaries :=
  S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (IDa_Deployed.boundaries r))

theorem deployed_slots (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation) :
    (Bd std r).mask = FIp_SemanticArithmetic.mask ∧ (Bd std r).add = FIp_SemanticArithmetic.add ∧
    (Bd std r).mul = FIp_SemanticArithmetic.mul ∧
    (Bd std r).claims = ClaimsUnrolledFinish.claims std ∧
    (Bd std r).terminal = (IDa_Deployed.boundaries r).terminal ∧
    (∀ {T F : Type} (N : Usize) (f : core.ops.function.FnMut F Usize T) (c : F),
      (Bd std r).fromFn N f c = OraclePortStdBuilder.fromFn N f c) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
#print axioms deployed_slots

theorem deployed_install (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation) :
    FIp_SemanticArithmetic.install (Bd std r) = Bd std r := rfl
#print axioms deployed_install

open Classical in
def gmask (a : Array Q 16#usize) (a1 : Array Q 10#usize) (q : Q) (alpha : Array Q 10#usize) : Result Q :=
  if AllC a ∧ AllC a1 ∧ Canon q ∧ AllC alpha then FIp_SemanticArithmetic.mask a a1 q alpha
  else fail Aeneas.Std.Error.panic

open Classical in
def gadd (x y : Q) : Result Q :=
  if Canon x ∧ Canon y then FIp_SemanticArithmetic.add x y else fail Aeneas.Std.Error.panic

open Classical in
def gmul (x y : Q) : Result Q :=
  if Canon x ∧ Canon y then FIp_SemanticArithmetic.mul x y else fail Aeneas.Std.Error.panic

def Bg (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation) : FinishModel.Boundaries :=
  { Bd std r with mask := gmask, add := gadd, mul := gmul }

/-! ### producers -/

theorem claims_canon (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    (pre : r1_wire.Prefix) (v1 : Claims) (h : (Bd std r).claims pre = ok (.Ok v1)) :
    ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q := by
  have h' : ClaimsUnrolledFinish.reference std pre = ok (.Ok v1) := by
    rw [← ClaimsUnrolledFinish.claims_value]; exact h
  exact FJa_ClaimsCanonical.value std pre v1 h'
#print axioms claims_canon

theorem alpha_canon (R : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (t t1 : r1_wire.SemanticTranscript H) (running : Q) (alpha : Array Q 10#usize)
    (h : RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1))) : AllC alpha := by
  have hc := SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical R D pre t t1 running alpha h
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have len : alpha.val.length = 10 := alpha.property
  have := hc ⟨i, by omega⟩
  rw [← hxi]
  exact this
#print axioms alpha_canon

theorem fromFn9_canon (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (v1 : Claims) (hc : ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q)
    (a : Array Q 16#usize) (h : (Bd std r).fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a) :
    AllC a :=
  fromFn_mem 16#usize (FinishModel.closureFn9 D) v1 Canon (closure9_mem D v1 Canon hc) a h
#print axioms fromFn9_canon

theorem fromFn5_canon (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (v1 : Claims) (hc : ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q)
    (a : Array Q 10#usize) (h : (Bd std r).fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a) :
    AllC a :=
  fromFn_mem 10#usize (FinishModel.closureFn5 D) v1 Canon (closure5_mem D v1 Canon hc) a h
#print axioms fromFn5_canon

theorem cell_canon (v1 : Claims) (hc : ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q)
    (a2 : Array Q 29#usize) (q : Q) (i j : Usize)
    (h2 : Array.index_usize v1 i = ok a2) (hq : Array.index_usize a2 j = ok q) : Canon q :=
  hc a2 (idx_mem _ _ _ h2) q (idx_mem _ _ _ hq)
#print axioms cell_canon

theorem decode_canon (vr : r1_wire.ValidatedRecord) (val3 : Array Q 29#usize) (q3 : Q)
    (h : AspisS1ExtractedRoundChildren.children.decode 29#usize vr 87#usize = ok (.Ok val3))
    (hq : Array.index_usize val3 28#usize = ok q3) : Canon q3 :=
  RawActualDecodeKMainAdapter.decodeMain_success_members_canonical 29#usize vr 87#usize val3 h q3
    (idx_mem _ _ _ hq)
#print axioms decode_canon

theorem mapped_rows (v1 : Claims) (hc : ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q) :
    ∀ row ∈ (FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ) v1).val,
      FIw_ArrayValue.canonical row := by
  intro row hrow
  obtain ⟨r0, hr0, hre⟩ := List.mem_map.mp hrow
  subst hre
  intro x hx
  obtain ⟨y, hy, hye⟩ := List.mem_map.mp hx
  subst hye
  exact hc r0 hr0 y hy
#print axioms mapped_rows

theorem mapped_array {n : Usize} (a : Array Q n) (h : AllC a) :
    FIw_ArrayValue.canonical (FIq_Carriers.mapArray FIq_Carriers.toQ a) := by
  intro x hx
  obtain ⟨y, hy, hye⟩ := List.mem_map.mp hx
  subst hye
  exact h y hy
#print axioms mapped_array

theorem terminal_canon (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (ch : r1_wire.Challenges)
    (hdom : NLU_Terminal.InputDomain pub ch) (v1 : Claims) (alpha : Array Q 10#usize)
    (hc : ∀ row ∈ v1.val, ∀ q ∈ row.val, Canon q) (ha : AllC alpha) (val2 : Q)
    (h : (Bd std r).terminal pub v1 alpha ch = ok (.Ok val2)) : Canon val2 := by
  have ho := NLU_Terminal.source r pub v1 alpha ch hdom (mapped_rows v1 hc) (mapped_array alpha ha)
  have e : (IDa_Deployed.boundaries r).terminal pub v1 alpha ch = ok (.Ok val2) := h
  rw [e] at ho
  exact ho
#print axioms terminal_canon

theorem mask_out_canon (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    (a : Array Q 16#usize) (a1 : Array Q 10#usize) (q : Q) (alpha : Array Q 10#usize)
    (ha : AllC a) (ha1 : AllC a1) (hq : Canon q) (hal : AllC alpha) (mk : Q)
    (h : (Bd std r).mask a a1 q alpha = ok mk) : Canon mk := by
  obtain ⟨out, hout, hcan⟩ := NPH_R22JoinSM2.FIp_mask_site (Bd std r) a a1 q alpha
    (fun j => by
      simp only [ExtractedMaskCoefficientStep.c1Cell, FIp_SemanticArithmetic.mapArray, List.getElem_map]
      exact ha _ (List.getElem_mem _))
    (fun j => by
      simp only [ExtractedMaskCoefficientStep.maskCell, FIp_SemanticArithmetic.mapArray, List.getElem_map]
      exact ha1 _ (List.getElem_mem _))
    (fun i hi => by
      simp only [ExtractedMaskLinearLoop.pointAtNat, FIp_SemanticArithmetic.mapArray, List.getElem_map]
      exact hal _ (List.getElem_mem _))
    hq
  have e : ok mk = ok out := h.symm.trans hout
  cases e
  exact hcan
#print axioms mask_out_canon

/-! ### the guarded record agrees with the deployed one at every reached argument -/

theorem deployed_finish_guarded (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (heta : Canon ch.eta) (hdom : NLU_Terminal.InputDomain pub ch) :
    FinishModel.finish AspisS1ExtractedRoundChildren.children (Bg std r) D pub pre t ch obs =
      FinishModel.finish AspisS1ExtractedRoundChildren.children (Bd std r) D pub pre t ch obs := by
  apply finish_congr
  · intro running alpha t1 v1 a a1 a2 q hH hF
    obtain ⟨hR, hC⟩ := hH
    obtain ⟨ha, ha1, ha2, hq⟩ := hF
    have hc := claims_canon std r pre v1 hC
    have hcond : AllC a ∧ AllC a1 ∧ Canon q ∧ AllC alpha :=
      ⟨fromFn9_canon std r D v1 hc a ha, fromFn5_canon std r D v1 hc a1 ha1,
        cell_canon v1 hc a2 q _ _ ha2 hq, alpha_canon _ D pre t t1 running alpha hR⟩
    show gmask a a1 q alpha = FIp_SemanticArithmetic.mask a a1 q alpha
    unfold gmask
    rw [if_pos hcond]
  · intro running alpha t1 v1 val2 hH hT
    obtain ⟨hR, hC⟩ := hH
    have hc := claims_canon std r pre v1 hC
    have hv := terminal_canon std r pub ch hdom v1 alpha hc (alpha_canon _ D pre t t1 running alpha hR) val2 hT
    show gmul ch.eta val2 = FIp_SemanticArithmetic.mul ch.eta val2
    unfold gmul
    rw [if_pos ⟨heta, hv⟩]
  · intro running alpha t1 v1 val2 a a1 a2 q mk q1 hH hT hF hmk hq1
    obtain ⟨hR, hC⟩ := hH
    obtain ⟨ha, ha1, ha2, hq⟩ := hF
    have hc := claims_canon std r pre v1 hC
    have hal := alpha_canon _ D pre t t1 running alpha hR
    have hv := terminal_canon std r pub ch hdom v1 alpha hc hal val2 hT
    have hmkc := mask_out_canon std r a a1 q alpha (fromFn9_canon std r D v1 hc a ha)
      (fromFn5_canon std r D v1 hc a1 ha1) (cell_canon v1 hc a2 q _ _ ha2 hq) hal mk hmk
    have hq1c := (FIp_SemanticValues.mul ch.eta val2 q1 heta hv hq1).1
    show gadd mk q1 = FIp_SemanticArithmetic.add mk q1
    unfold gadd
    rw [if_pos ⟨hmkc, hq1c⟩]
  · intro running alpha t1 v1 val2 a a1 a2 q mk q1 q2 vr val3 q3 hH hT hF hmk hq1 hTl
    obtain ⟨hR, hC⟩ := hH
    obtain ⟨ha, ha1, ha2, hq⟩ := hF
    obtain ⟨hq2, hV, hD, hq3⟩ := hTl
    have hc := claims_canon std r pre v1 hC
    have hal := alpha_canon _ D pre t t1 running alpha hR
    have hv := terminal_canon std r pub ch hdom v1 alpha hc hal val2 hT
    have hmkc := mask_out_canon std r a a1 q alpha (fromFn9_canon std r D v1 hc a ha)
      (fromFn5_canon std r D v1 hc a1 ha1) (cell_canon v1 hc a2 q _ _ ha2 hq) hal mk hmk
    have hq1c := (FIp_SemanticValues.mul ch.eta val2 q1 heta hv hq1).1
    have hq2c := (FIp_SemanticValues.add mk q1 q2 hmkc hq1c hq2).1
    have hq3c := decode_canon vr val3 q3 hD hq3
    show gadd q2 q3 = FIp_SemanticArithmetic.add q2 q3
    unfold gadd
    rw [if_pos ⟨hq2c, hq3c⟩]
#print axioms deployed_finish_guarded

theorem deployed_verify_guarded (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hdig : LIB_VPublicDomain.publicDigestDom pub) :
    VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children (Bg std r)) D pub bytes hash obs =
      VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children (Bd std r)) D pub bytes hash obs := by
  apply verify_congr
  intro p t t' c hp ht hb
  obtain ⟨hl, hchi, hth, hmu, heta, hz⟩ := FJn_BeginCanonical.value D p t t' c hb
  obtain ⟨bytes', hbytes, -⟩ := PreparationSuccess.public_transcript_success D pub hash p.c1_root t ht
  have hasset := LIB_VPublicAsset.bytes_asset pub bytes' hbytes
  have hdom : NLU_Terminal.InputDomain pub c :=
    ⟨hdig, hasset, mapped_array c.zc hz, hl, hchi, hth, hmu⟩
  exact deployed_finish_guarded std r D pub p t' c obs heta hdom
#print axioms deployed_verify_guarded

/-! ### site statements on the guarded record -/

theorem guarded_mask_site (a : Array Q 16#usize) (a1 : Array Q 10#usize) (q : Q) (alpha : Array Q 10#usize) :
    gmask a a1 q alpha = fail Aeneas.Std.Error.panic ∨
    (AllC a ∧ AllC a1 ∧ Canon q ∧ AllC alpha ∧
      gmask a a1 q alpha = FIp_SemanticArithmetic.mask a a1 q alpha ∧
      ∃ out, FIp_SemanticArithmetic.mask a a1 q alpha = ok out ∧ Canon out) := by
  by_cases hc : AllC a ∧ AllC a1 ∧ Canon q ∧ AllC alpha
  · right
    refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, by unfold gmask; rw [if_pos hc], ?_⟩
    obtain ⟨out, hout, hcan⟩ := NPH_R22JoinSM2.FIp_mask_site (IDa_Deployed.boundaries (.Ok ())) a a1 q alpha
      (fun j => by
        simp only [ExtractedMaskCoefficientStep.c1Cell, FIp_SemanticArithmetic.mapArray, List.getElem_map]
        exact hc.1 _ (List.getElem_mem _))
      (fun j => by
        simp only [ExtractedMaskCoefficientStep.maskCell, FIp_SemanticArithmetic.mapArray, List.getElem_map]
        exact hc.2.1 _ (List.getElem_mem _))
      (fun i hi => by
        simp only [ExtractedMaskLinearLoop.pointAtNat, FIp_SemanticArithmetic.mapArray, List.getElem_map]
        exact hc.2.2.2 _ (List.getElem_mem _))
      hc.2.2.1
    exact ⟨out, hout, hcan⟩
  · left
    unfold gmask
    rw [if_neg hc]
#print axioms guarded_mask_site

theorem canon_w (x : Q) (h : Canon x) : NPH_R22Towers.SM_WQ (FIp_SemanticArithmetic.toProbe x) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact ⟨⟨Nat.le_of_lt h1, Nat.le_of_lt h2⟩, ⟨Nat.le_of_lt h3, Nat.le_of_lt h4⟩⟩
#print axioms canon_w

theorem guarded_add_site (x y : Q) :
    gadd x y = fail Aeneas.Std.Error.panic ∨
    (Canon x ∧ Canon y ∧ gadd x y = FIp_SemanticArithmetic.add x y ∧
      ∃ z, FIp_SemanticArithmetic.add x y = ok z ∧ NPH_R22Towers.SM_WQ (FIp_SemanticArithmetic.toProbe z)) := by
  by_cases hc : Canon x ∧ Canon y
  · right
    exact ⟨hc.1, hc.2, by unfold gadd; rw [if_pos hc],
      NPH_R22JoinSM.FIp_add_W x y (canon_w x hc.1) (canon_w y hc.2)⟩
  · left
    unfold gadd
    rw [if_neg hc]
#print axioms guarded_add_site

theorem guarded_mul_site (x y : Q) :
    gmul x y = fail Aeneas.Std.Error.panic ∨
    (Canon x ∧ Canon y ∧ gmul x y = FIp_SemanticArithmetic.mul x y ∧
      ∃ z, FIp_SemanticArithmetic.mul x y = ok z ∧ NPH_R22Towers.SM_WQ (FIp_SemanticArithmetic.toProbe z)) := by
  by_cases hc : Canon x ∧ Canon y
  · right
    exact ⟨hc.1, hc.2, by unfold gmul; rw [if_pos hc],
      NPH_R22JoinSM.FIp_mul_W x y (canon_w x hc.1) (canon_w y hc.2)⟩
  · left
    unfold gmul
    rw [if_neg hc]
#print axioms guarded_mul_site

end AspisR1.NPH_R22JoinSM4
