import Lean
import NGU_Part006
import NGU_Part005
import AspisR1DecodeKFullSuccessCanonicality
import NGU_Part004
import RPz7_ClaimsUnrolledFinishAdapters
import RPz7_NP6_ClaimsModel
import RPz7_S1SemanticFinishModelV1
-- Retargeted LPr_SelectedWords
set_option autoImplicit false
namespace AspisR1.NGU_LPr_SelectedWords
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : U8 := bs[i]?.getD 0#u8

def naturalWord (bs : List U8) (i : Nat) : Nat :=
  (byte bs i).val + 256*(byte bs (i+1)).val +
    65536*(byte bs (i+2)).val + 16777216*(byte bs (i+3)).val

def nativeWord (b : Slice U8) (j : Nat) : U32 := core.num.U32.from_le_bytes
  (Array.make 4#usize [byte b.val (4*j),byte b.val (4*j+1),
    byte b.val (4*j+2),byte b.val (4*j+3)])

theorem window_byte (bs : List U8) (offset lane : Nat) (h : lane<32) :
    byte ((bs.drop offset).take 32) lane = byte bs (offset+lane) := by
  simp only [byte,List.getElem?_take,h,↓reduceIte,List.getElem?_drop]

theorem window_word (bs : List U8) (b : Slice U8) (offset j : Nat)
    (same : b.val=(bs.drop offset).take 32) (hj : j<8) :
    (nativeWord b j).val=naturalWord bs (offset+4*j) := by
  unfold nativeWord
  rw [NGU_LPr_WordNat.value]
  simp only [same,window_byte bs offset (4*j) (by omega),
    window_byte bs offset (4*j+1) (by omega),
    window_byte bs offset (4*j+2) (by omega),
    window_byte bs offset (4*j+3) (by omega),naturalWord,Nat.add_assoc]

/-- Converts global natural LE word bounds into the exact native selected-byte
    domain. It does not claim the still-uninstalled check/expand caller join. -/
theorem selected_words (y1 : Slice U8) (len : y1.val.length=928)
    (canonical : ∀ row j : Nat, row<29 → j<8 →
      naturalWord y1.val (32*row+4*j)<2147483647) :
    ∀ l : Usize, l.val<29 → ∃ b : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
        {start:=Usize.wrapping_mul l 32#usize,
         «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}=ok b ∧
      b.val.length=32 ∧ (∀ j, j<8 → (nativeWord b j).val<2147483647) := by
  intro l hl
  obtain ⟨b,run,size,same⟩ := NGU_LPr_SelectedBytes.selected y1 len l hl
  refine ⟨b,run,size,?_⟩
  intro j hj
  rw [window_word y1.val b (32*l.val) j same hj]
  exact canonical l.val j hl hj

#print axioms window_byte
#print axioms window_word
#print axioms selected_words
end AspisR1.NGU_LPr_SelectedWords

-- Retargeted LPs_NaturalDomain
set_option autoImplicit false
namespace AspisR1.NGU_LPs_NaturalDomain
open Aeneas Aeneas.Std Result

/-- Nominal application of the inherited LPr byte/word ports to LPq. The
check/expand producer cannot yet co-import with this consumer; its facts
remain explicit here rather than being credited as a discharged native join. -/
theorem selected (compact y1 : Slice U8) (len : y1.val.length=928)
    (expanded : NGU_LPq_ExpandedWords.Expanded compact.val y1.val)
    (canonical : NGU_LPq_ExpandedWords.CompactCanonical compact.val) :
    NGU_LPq_SelectedDomain.ByteDomain y1 := by
  apply NGU_LPr_SelectedWords.selected_words y1 len
  intro row j hr hj
  exact NGU_LPq_ExpandedWords.canonical compact.val y1.val expanded canonical row j hr hj

#print axioms selected
end AspisR1.NGU_LPs_NaturalDomain

-- Retargeted LPs_ClaimsDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_LPs_ClaimsDomain
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues

def RowCanonical (a : Array MainQM 29#usize) : Prop := ∀ j : Fin 29,
  canonQ (NGU_LPq_ReadPorts.backQ (toClaimQ (a.val[j.val]'(by have h:=a.property;change a.val.length=29 at h;omega))))


theorem decoded (r : AspisR1ClaimsUnrolledParent.Record) (off : Usize)
    (row : Array ParentQM 29#usize)
    (call : sourceDecode 29#usize r off=ok (.Ok row)) :
    RowCanonical (toMainArray row) := by
  have port := congrArg toMainDecoded call
  rw [decode_exact] at port
  unfold AspisS1ExtractedRoundChildren.decodeMain at port
  cases h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k 29#usize
      (AspisS1ExtractedRoundChildren.recordToDecoder (toMainRecord r)) off with
  | fail e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
  | div => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
  | ok result =>
    cases result with
    | Err e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port;cases port
    | Ok values =>
      simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at port
      have same := core.result.Result.Ok.inj (Result.ok.inj port)
      have canonical := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical
        29#usize _ off values h
      intro j
      have cell := canonical j
      rw [←same]
      simpa only [AspisS1ExtractedRoundChildren.decoderArrayToMain,List.getElem_map,
        AspisS1ExtractedRoundChildren.decoderQMToMain,toClaimQ,NGU_LPq_ReadPorts.backQ,
        canonQ,canonC,NFN_LPi_CMProduct.Canon,AspisR1DecodeKCanonicalArrayInvariant.Canonical,
        AspisR1DecodeKFullV10.aspis_core.field.P,
        show (2147483647#u32).val=2147483647 from rfl,and_assoc] using cell

theorem claims (pre : MainPrefix) (out : MainClaims)
    (success : ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out)) :
    ∀ row ∈ out.val, RowCanonical row := by
  rw [claims_value] at success
  unfold reference at success
  rw [NP6_ClaimsModel.reference_normalized] at success
  unfold NP6_ClaimsModel.normalized at success
  dsimp only at success
  cases record : (external (NP6_StdModel.calls (.Ok ()))).validated (fromMainPrefix pre) 25#u8 with
  | fail e =>
    simp only [record,bind_tc_fail,toMainStatus,reduceCtorEq] at success
  | div =>
    simp only [record,bind_tc_div,toMainStatus,reduceCtorEq] at success
  | ok result =>
    cases result with
    | Err e =>
      simp only [record,bind_tc_ok,toMainStatus] at success
      cases success
    | Ok r =>
      simp only [record,bind_tc_ok] at success
      change toMainStatus (AspisR1ClaimsUnrolledParent.decodeRows
        (external (NP6_StdModel.calls (.Ok ()))) r)=ok (.Ok out) at success
      unfold AspisR1ClaimsUnrolledParent.decodeRows external at success
      cases da : sourceDecode 29#usize r 0#usize with
      | fail e =>
        simp only [da,bind_tc_fail,toMainStatus,reduceCtorEq] at success
      | div =>
        simp only [da,bind_tc_div,toMainStatus,reduceCtorEq] at success
      | ok result =>
        cases result with
        | Err e =>
          simp only [da,bind_tc_ok,toMainStatus] at success
          cases success
        | Ok a =>
          simp only [da,bind_tc_ok] at success
          cases db : sourceDecode 29#usize r 29#usize with
          | fail e =>
            simp only [db,bind_tc_fail,toMainStatus,reduceCtorEq] at success
          | div =>
            simp only [db,bind_tc_div,toMainStatus,reduceCtorEq] at success
          | ok result =>
            cases result with
            | Err e =>
              simp only [db,bind_tc_ok,toMainStatus] at success
              cases success
            | Ok b =>
              simp only [db,bind_tc_ok] at success
              cases dc : sourceDecode 29#usize r 58#usize with
              | fail e =>
                simp only [dc,bind_tc_fail,toMainStatus,reduceCtorEq] at success
              | div =>
                simp only [dc,bind_tc_div,toMainStatus,reduceCtorEq] at success
              | ok result =>
                cases result with
                | Err e =>
                  simp only [dc,bind_tc_ok,toMainStatus] at success
                  cases success
                | Ok c =>
                  simp only [dc,bind_tc_ok] at success
                  have same := core.result.Result.Ok.inj (Result.ok.inj success)
                  subst out
                  intro row member
                  change row ∈ [toMainArray a,toMainArray b,toMainArray c] at member
                  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
                  rcases member with rfl|rfl|rfl
                  · exact decoded r 0#usize a da
                  · exact decoded r 29#usize b db
                  · exact decoded r 58#usize c dc

#print axioms decoded
#print axioms claims
end AspisR1.NGU_LPs_ClaimsDomain
end

-- Retargeted JGi_FinishFields
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NGU_JGi_FinishFields
open AspisR1PublicPreparation

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok p => cases p with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Returned claim operands come from the SAME successful semantic finish. -/
theorem source (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (h : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ (record25 record26 : r1_wire.ValidatedRecord),
      B.claims pre=ok (.Ok out.claims) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
      R.decode 29#usize record25 87#usize=ok (.Ok out.extra) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
      R.decode 29#usize record26 0#usize=ok (.Ok out.before_z1) := by
  unfold FinishModel.finish at h
  obtain ⟨roundsResult, hrounds, h⟩ := bind_success _ _ _ h
  cases roundsResult with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok val =>
    rcases val with ⟨running,alpha,t25⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
    obtain ⟨claimsResult,hclaims,h⟩ := bind_success _ _ _ h
    cases claimsResult with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      cases h
    | Ok claims =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨terminalResult,hterminal,h⟩ := bind_success _ _ _ h
      cases terminalResult with
      | Err e =>
        simp only [core.result.Result.map_err,FinishModel.closureFn11,FinishModel.closureFn10,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        cases h
      | Ok terminal =>
        simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok,VerifyPrefix.mark] at h
        obtain ⟨mask16,hm16,h⟩ := bind_success _ _ _ h
        obtain ⟨mask10,hm10,h⟩ := bind_success _ _ _ h
        obtain ⟨claim0,hc0,h⟩ := bind_success _ _ _ h
        obtain ⟨claim27,hc27,h⟩ := bind_success _ _ _ h
        obtain ⟨mask,hm,h⟩ := bind_success _ _ _ h
        obtain ⟨record25Result,hr25,h⟩ := bind_success _ _ _ h
        cases record25Result with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at h
          cases h
        | Ok record25 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          obtain ⟨extraResult,hextra,h⟩ := bind_success _ _ _ h
          cases extraResult with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,bind_tc_ok] at h
            cases h
          | Ok extra =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            obtain ⟨etaTerminal,het,h⟩ := bind_success _ _ _ h
            obtain ⟨masked,hmasked,h⟩ := bind_success _ _ _ h
            obtain ⟨extra28,he28,h⟩ := bind_success _ _ _ h
            obtain ⟨maskedTerminal,hmt,h⟩ := bind_success _ _ _ h
            obtain ⟨different,hdiff,h⟩ := bind_success _ _ _ h
            cases different with
            | true => cases h
            | false =>
              simp only [VerifyPrefix.mark,r1_wire.SemanticTranscript.impl.state,
                core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              obtain ⟨circle0Result,t26,hz0,h⟩ := pair_success _ _ _ h
              cases circle0Result with
              | Err e =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from,bind_tc_ok] at h
                cases h
              | Ok z0 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                obtain ⟨record26Result,hr26,h⟩ := bind_success _ _ _ h
                cases record26Result with
                | Err e =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from,bind_tc_ok] at h
                  cases h
                | Ok record26 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                  obtain ⟨beforeZ1Result,hbeforeZ1,h⟩ := bind_success _ _ _ h
                  cases beforeZ1Result with
                  | Err e =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from,bind_tc_ok] at h
                    cases h
                  | Ok beforeZ1 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                    obtain ⟨circle1Result,t27,hz1,h⟩ := pair_success _ _ _ h
                    cases circle1Result with
                    | Err e =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from,bind_tc_ok] at h
                      cases h
                    | Ok z1 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
                      obtain ⟨equal,hequal,h⟩ := bind_success _ _ _ h
                      cases equal with
                      | true => cases h
                      | false =>
                        obtain ⟨rootResult,hroot,h⟩ := bind_success _ _ _ h
                        cases rootResult with
                        | Err e =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from,bind_tc_ok] at h
                          cases h
                        | Ok rootPayload =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                          obtain ⟨copied,hcopy,h⟩ := bind_success _ _ _ h
                          obtain ⟨root2,hroot2,h⟩ := bind_success _ _ _ h
                          have he := core.result.Result.Ok.inj (Result.ok.inj h)
                          cases he
                          exact ⟨record25,record26,hclaims,hr25,hextra,hr26,hbeforeZ1⟩


#print axioms source
#print axioms bind_success
#print axioms pair_success
end AspisR1.NGU_JGi_FinishFields

-- Retargeted LPs_SemanticDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_LPs_SemanticDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues

theorem decoded (r : r1_wire.ValidatedRecord) (off : Usize)
    (a : Array aspis_core.field.QM31 29#usize)
    (call : AspisS1ExtractedRoundChildren.decodeMain 29#usize r off=ok (.Ok a)) :
    NGU_LPs_ClaimsDomain.RowCanonical a := by
  let parent : AspisR1ClaimsUnrolledParent.Record := ⟨r.row,r.framed⟩
  have same : ClaimsUnrolledFinish.toMainRecord parent=r := by cases r;rfl
  have port : ClaimsUnrolledFinish.sourceDecode 29#usize parent off=
      ok (.Ok (ClaimsUnrolledFinish.fromMainArray a)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [same,call]
  have canonical := NGU_LPs_ClaimsDomain.decoded parent off _ port
  simpa only [ClaimsUnrolledFinish.array_back] using canonical

theorem row (a : Array aspis_core.field.QM31 29#usize)
    (ha : NGU_LPs_ClaimsDomain.RowCanonical a) :
    ∀ q ∈ (mapArray toClaimQ a).val,canonQ (NGU_LPq_ReadPorts.backQ q) := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp hx
  have bound : i<29 := by have := a.property;change a.val.length=29 at this;omega
  subst x
  exact ha ⟨i,bound⟩

theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre before challenges obs=ok (.Ok sem)) :
    NGU_LPq_ReadPorts.SemCanonical (toClaimSem sem) := by
  obtain ⟨r25,r26,claims,read25,extra,read26,before⟩ := NGU_JGi_FinishFields.source
    AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))} D pub pre before challenges obs sem finish
  have cc := NGU_LPs_ClaimsDomain.claims pre sem.claims claims
  refine ⟨?_,row sem.extra (decoded _ _ _ extra),
    row sem.before_z1 (decoded _ _ _ before)⟩
  intro a ha
  obtain ⟨original,mem,rfl⟩ := List.mem_map.mp ha
  exact row original (cc original mem)

#print axioms decoded
#print axioms row
#print axioms source
end AspisR1.NGU_LPs_SemanticDomain
end

-- Retargeted LPs_PreparedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_LPs_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues

/-- Conditional consumer join. Semantic and powers canonicality are derived.
Natural byte predicates remain explicit because the producer cannot co-import
with LPq; this is NOT a native prepared_claim closure theorem. -/
theorem native_result (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact y1 : Slice U8) (len : y1.val.length=928)
    (expanded : NGU_LPq_ExpandedWords.Expanded compact.val y1.val)
    (checked : NGU_LPq_ExpandedWords.CompactCanonical compact.val)
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ out, NGU_LPq_PreparedTrace.Trace (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      NGU_LPq_PreparedClaim.program (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (NGU_Powers.claim out)) := by
  exact NGU_LPq_SelectedDomain.native_result (toClaimSem sem)
    (NGU_LPs_SemanticDomain.source B D pub pre beforeSemantic challenges obs sem finish)
    y1 (NGU_LPs_NaturalDomain.selected compact y1 len expanded checked)
    (NGU_Carriers.arr NGU_Powers.claim g)
    (NGU_LPq_CarrierFacts.weights_from_powers gamma hc g powers) inactive kappa hi hk

#print axioms native_result
#print axioms NGU_LPq_CarrierFacts.native_unique
end AspisR1.NGU_LPs_PreparedClaim
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
