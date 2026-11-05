import Lean
import NGU_Part005
import Aeneas
import Mathlib.Tactic.IntervalCases
-- Retargeted LPq_OuterTrace
set_option autoImplicit false
namespace AspisR1.NGU_LPq_OuterTrace
open Aeneas Aeneas.Std Result ControlFlow NFN_LPi_FieldValues NGU_LPm_RawPort NGU_Carriers
open AspisR1CurrentPreparedClaim
abbrev Range := NGU_LPm_PointLoop.Range
abbrev Seven := NGU_WeightedStep.Seven

/-- Source-local outer observations. Each nested Dot trace uses the SAME
semantic carrier, selected bytes and coefficient array. The final component
is the previously paired seven-step native weighting, not a body equality. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (k : Seven) : Range → Seven → NE → Prop where
  | done (iter iter' : Range) (parts : Seven) (out : NE)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (none,iter'))
      (sum : NGU_Weighted.run k parts 7 0#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
      Trace sem y1 g k iter parts out
  | step {iter iter' : Range} {parts : Seven} {out : NE}
      (point i : Usize) (value : NE) (xs : List (NE×NQ))
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some point,iter'))
      (dot : NGU_LPm_PointLoop.Trace sem y1 g point
        {start:=0#usize,«end»:=29#usize} NGU_LPm_PublicTwentyNine.zero xs value)
      (increment : (point+1#usize : Result Usize)=ok i) (within : i.val<7)
      (tail : Trace sem y1 g k iter' (parts.set i value) out) :
      Trace sem y1 g k iter parts out

theorem point_source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {point : Usize} {xs : List (NE×NQ)} {value : NE}
    (tr : NGU_LPm_PointLoop.Trace sem y1 g point
      {start:=0#usize,«end»:=29#usize} NGU_LPm_PublicTwentyNine.zero xs value) :
    verifier.prepared_claim_dot NGU_LPm_PointLoop.ops inst sem y1 g point=ok (.Ok (NGU_Powers.claim value)) := by
  change verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst
    {start:=0#usize,«end»:=29#usize} sem y1 g point
    (statePort NGU_LPm_PublicTwentyNine.zero)=_
  exact NGU_LPm_PointLoop.source inst tr

/-- Whole outer Result follows from linked local calls. There is no supplied
whole prepared_claim Result, independent part inventory or public sum. -/
theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {k parts : Seven} {iter : Range} {out : NE}
    (hk : NGU_WeightedStep.canonical k) (hp : NGU_WeightedStep.canonical parts)
    (tr : Trace sem y1 g k iter parts out) :
    verifier.prepared_claim_loop NGU_LPm_PointLoop.ops inst iter sem y1 g
      (arr NGU_Powers.claim k) (arr NGU_Powers.claim parts)=ok (.Ok (NGU_Powers.claim out)) := by
  induction tr with
  | done iter iter' parts out next sum =>
    obtain ⟨actual,en,_,model⟩ := NGU_Weighted.source k parts hk hp
    have same : actual=out := Result.ok.inj (en.symm.trans sum)
    rw [same] at model
    have body : verifier.prepared_claim_loop.body NGU_LPm_PointLoop.ops inst sem y1 g
        (arr NGU_Powers.claim k) iter (arr NGU_Powers.claim parts)=
        ok (ControlFlow.done (.Ok (NGU_Powers.claim out))) := by
      rw [verifier.prepared_claim_loop.body,next,bind_tc_ok]
      rw [model,bind_tc_ok]
      rfl
    change Aeneas.Std.loop _ _=_
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
  | @step iter iter' parts out point i value xs next dot increment within tail ih =>
    have model := point_source inst dot
    have write := NGU_LPq_ArrayPorts.mapped NGU_Powers.claim parts i value within
    have hp' := NGU_LPq_ArrayPorts.canonical_set parts i value hp (NGU_LPq_OutputDomains.point dot)
    have body : verifier.prepared_claim_loop.body NGU_LPm_PointLoop.ops inst sem y1 g
        (arr NGU_Powers.claim k) iter (arr NGU_Powers.claim parts)=
        ok (ControlFlow.cont (iter',arr NGU_Powers.claim (parts.set i value))) := by
      rw [verifier.prepared_claim_loop.body,next,bind_tc_ok]
      change (do
        let r ← verifier.prepared_claim_dot NGU_LPm_PointLoop.ops inst sem y1 g point
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => do
          let j ← point+1#usize
          let a ← Array.update (arr NGU_Powers.claim parts) j val
          ok (ControlFlow.cont (iter',a))
        | core.ops.control_flow.ControlFlow.Break residual => do
          let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.field.WideExact (core.convert.FromSame verifier.Error) residual
          ok (ControlFlow.done r1))=_
      rw [model,bind_tc_ok]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,increment,write]

    change Aeneas.Std.loop _ _=_
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
    exact ih hp'

#print axioms point_source
#print axioms source
end AspisR1.NGU_LPq_OuterTrace

-- Retargeted LPq_OuterConstruct
set_option autoImplicit false
namespace AspisR1.NGU_LPq_OuterConstruct
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

theorem loop {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (k : NGU_WeightedStep.Seven)
    (hk : NGU_WeightedStep.canonical k)
    (domain : ∀ p : Usize, p.val<6 → NGU_LPq_PointConstruct.ReadDomain sem y1 g p)
    (fuel : Nat) (iter : NGU_LPq_OuterTrace.Range) (parts : NGU_WeightedStep.Seven)
    (hp : NGU_WeightedStep.canonical parts) (last : iter.end.val=6)
    (bound : iter.start.val≤6) (remaining : 6-iter.start.val≤fuel) :
    ∃ out, NGU_LPq_OuterTrace.Trace sem y1 g k iter parts out ∧ canonE out := by
  induction fuel generalizing iter parts with
  | zero =>
    have stopped : ¬ (iter.start.val < iter.end.val) := by omega
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
        (by intros;rfl) (by intros;rfl) iter)
    simp only [stopped,↓reduceIte] at shape
    obtain ⟨out,sum,co,_⟩ := NGU_Weighted.source k parts hk hp
    exact ⟨out,.done iter iter' parts out (by rw [shape.1.1] at call;exact call) sum,co⟩
  | succ n ih =>
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
        (by intros;rfl) (by intros;rfl) iter)
    by_cases active : iter.start.val < iter.end.val
    · simp only [active,↓reduceIte] at shape
      have hi : iter.start.val<6 := by omega
      obtain ⟨xs,value,dot⟩ := NGU_LPq_PointConstruct.from_zero sem y1 g iter.start (domain _ hi)
      obtain ⟨i,inc,vi⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x:=iter.start) (y:=1#usize) (by scalar_tac))
      have advance : i.val=iter.start.val+1 := by simpa only [UScalar.ofNatCore_val_eq] using vi
      have within : i.val<7 := by omega
      have ci := NGU_LPq_ArrayPorts.canonical_set parts i value hp (NGU_LPq_OutputDomains.point dot)
      have next : iter'.start.val=iter.start.val+1 := shape.1.2
      have last' : iter'.end.val=6 := by rw [shape.2];exact last
      obtain ⟨out,tail,co⟩ := ih iter' (parts.set i value) ci last' (by omega) (by omega)
      exact ⟨out,.step iter.start i value xs (by rw [shape.1.1] at call;exact call)
        dot inc within tail,co⟩
    · simp only [active,↓reduceIte] at shape
      obtain ⟨out,sum,co,_⟩ := NGU_Weighted.source k parts hk hp
      exact ⟨out,.done iter iter' parts out (by rw [shape.1.1] at call;exact call) sum,co⟩

#print axioms loop
end AspisR1.NGU_LPq_OuterConstruct

-- Retargeted LPq_PreparedTrace
set_option autoImplicit false
namespace AspisR1.NGU_LPq_PreparedTrace
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort NGU_Carriers
open AspisR1CurrentPreparedClaim
abbrev Seven := NGU_WeightedStep.Seven
abbrev zero := FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO

def initial (inactive : NE) : Seven := (Array.repeat 7#usize zero).set 0#usize inactive

theorem zero_claim : NGU_Powers.claim zero=aspis_core.field.WideExact.ZERO := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
    FIo_Native.aspis_core.field.QM31.ZERO aspis_core.field.WideExact.ZERO aspis_core.field.QM31.ZERO
  rfl

theorem initial_canonical (inactive : NE) (hi : canonE inactive) :
    NGU_WeightedStep.canonical (initial inactive) := by
  apply NGU_LPq_ArrayPorts.canonical_set _ _ _ _ hi
  intro z hz
  have same : z=zero := (List.mem_replicate.mp hz).2
  rw [same]
  exact NGU_Weighted.zero_canonical

/-- Whole-body carrier trace: a local powers call, the source's actual initial
parts carrier and six linked point/store transitions ending in native weighting.
No whole-body equation or independently supplied final parts occurs here. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (inactive kappa out : NE) : Prop where
  | mk (k : Seven) (powers : FIo_Native.weights.powers 7#usize kappa=ok k)
      (outer : NGU_LPq_OuterTrace.Trace sem y1 g k
        {start:=0#usize,«end»:=6#usize} (initial inactive) out) :
      Trace sem y1 g inactive kappa out

theorem construct {H : Type} (sem : r1_semantic.Verified H)
    (hs : NGU_LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : NGU_LPq_SixPoints.SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : NGU_LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, Trace sem y1 g inactive kappa out ∧ canonE out := by
  obtain ⟨k,call,_⟩ := NGU_Powers.source 7#usize kappa hk
  have kc := NGU_LPq_OutputDomains.powers kappa hk k call
  obtain ⟨out,outer,co⟩ := NGU_LPq_OuterConstruct.loop sem y1 g k kc
    (fun p hp => NGU_LPq_SixPoints.domain sem hs y1 hy g hg p hp)
    6 {start:=0#usize,«end»:=6#usize} (initial inactive) (initial_canonical inactive hi)
    rfl (by decide) (by decide)
  exact ⟨out,⟨k,call,outer⟩,co⟩

/-- Full concrete cohort Result from ONE native local carrier trace. Local
powers uniqueness identifies the actual k, not a separately chosen array. -/
theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {inactive kappa out : NE} (hi : canonE inactive) (hk : canonE kappa)
    (tr : Trace sem y1 g inactive kappa out) :
    AspisR1CurrentPreparedClaim.verifier.prepared_claim NGU_LPm_PointLoop.ops inst sem y1 (NGU_Powers.claim inactive) g
      (NGU_Powers.claim kappa)=ok (.Ok (NGU_Powers.claim out)) := by
  rcases tr with ⟨k,powers,outerTrace⟩
  obtain ⟨actual,native,model⟩ := NGU_Powers.source 7#usize kappa hk
  have same : actual=k := Result.ok.inj (native.symm.trans powers)
  rw [same] at model
  have outer := NGU_LPq_OuterTrace.source inst (NGU_LPq_OutputDomains.powers kappa hk k powers)
    (initial_canonical inactive hi) outerTrace
  have init := NGU_LPq_ArrayPorts.mapped NGU_Powers.claim (Array.repeat 7#usize zero)
    0#usize inactive (by decide)
  rw [NGU_ArrayMap.repeated,zero_claim] at init
  unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim
  change (do
    let k ← ClaimPowers.powers 7#usize (NGU_Powers.claim kappa)
    let parts ← Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize (NGU_Powers.claim inactive)
    verifier.prepared_claim_loop NGU_LPm_PointLoop.ops inst
      {start:=0#usize,«end»:=6#usize} sem y1 g k parts)=_
  rw [model,bind_tc_ok,init,bind_tc_ok]
  exact outer

#print axioms zero_claim
#print axioms initial_canonical
#print axioms construct
#print axioms source
end AspisR1.NGU_LPq_PreparedTrace

-- Retargeted LPq_PreparedClaim
set_option autoImplicit false
namespace AspisR1.NGU_LPq_PreparedClaim
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
open AspisR1CurrentPreparedClaim

/-- Frozen source has no digest invocation in this leaf. This function family
keeps the nominal digest instance arbitrary rather than specializing to one
reply or one native successful output. Native association remains the hybrid
local-gate/source-partition obligation documented in the leaf packet. -/
def program {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (inactive kappa : NE) :=
  fun inst : aspis_core.Digest32 H => AspisR1CurrentPreparedClaim.verifier.prepared_claim NGU_LPm_PointLoop.ops inst
    sem y1 (NGU_Powers.claim inactive) g (NGU_Powers.claim kappa)

theorem program_eq {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {inactive kappa out : NE}
    (hi : canonE inactive) (hk : canonE kappa)
    (tr : NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa out) :
    program sem y1 g inactive kappa = fun _ => ok (.Ok (NGU_Powers.claim out)) := by
  funext inst
  exact NGU_LPq_PreparedTrace.source inst hi hk tr

/-- ONE constructed local trace supplies the SAME result for every digest
instance. No accepted whole-body run, whole-output equality or independent
final array is a premise. SelectedFields is still explicit in this interface. -/
theorem native_result {H : Type} (sem : r1_semantic.Verified H)
    (hs : NGU_LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : NGU_LPq_SixPoints.SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : NGU_LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa out ∧ canonE out ∧
      program sem y1 g inactive kappa = fun _ => ok (.Ok (NGU_Powers.claim out)) := by
  obtain ⟨out,tr,co⟩ := NGU_LPq_PreparedTrace.construct sem hs y1 hy g hg inactive kappa hi hk
  exact ⟨out,tr,co,program_eq hi hk tr⟩

theorem uniqueness {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {inactive kappa left right : NE} (hi : canonE inactive) (hk : canonE kappa)
    (lt : NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa left)
    (rt : NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa right) :
    NGU_Powers.claim left=NGU_Powers.claim right := by
  have l := NGU_LPq_PreparedTrace.source inst hi hk lt
  have r := NGU_LPq_PreparedTrace.source inst hi hk rt
  exact core.result.Result.Ok.inj (Result.ok.inj (l.symm.trans r))

#print axioms program_eq
#print axioms native_result
#print axioms uniqueness
end AspisR1.NGU_LPq_PreparedClaim

-- Retargeted LPq_SelectedDomain
set_option autoImplicit false
namespace AspisR1.NGU_LPq_SelectedDomain
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

def selected (y1 : Slice U8) (l : Usize) : Result (Slice U8) :=
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
    {start:=Usize.wrapping_mul l 32#usize,
     «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}

/-- Only the selected input bytes and word bounds, with the actual native slice
operation. No decoded field output or field-success observation is a premise. -/
def ByteDomain (y1 : Slice U8) : Prop := ∀ l : Usize, l.val<29 → ∃ b : Slice U8,
  selected y1 l=ok b ∧ b.val.length=32 ∧
    (∀ j, j<8 → (NGU_LPq_BytesTotal.word b j).val<2147483647)

theorem selected_fields (y1 : Slice U8) (hy : ByteDomain y1) : NGU_LPq_SixPoints.SelectedFields y1 := by
  intro l hl
  obtain ⟨b,slice,len,words⟩ := hy l hl
  obtain ⟨out,decode,co⟩ := NGU_LPq_BytesTotal.source b len words
  refine ⟨out,co,?_⟩
  change (do
    let b ← selected y1 l
    let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b
    core.option.Option.unwrap o)=_
  rw [slice,bind_tc_ok,decode,bind_tc_ok]
  rfl

theorem native_result {H : Type} (sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H)
    (hs : NGU_LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : ByteDomain y1)
    (g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize) (hg : NGU_LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa out ∧ canonE out ∧
      NGU_LPq_PreparedClaim.program sem y1 g inactive kappa = fun _ => ok (.Ok (NGU_Powers.claim out)) :=
  NGU_LPq_PreparedClaim.native_result sem hs y1 (selected_fields y1 hy) g hg inactive kappa hi hk

#print axioms selected_fields
#print axioms native_result
end AspisR1.NGU_LPq_SelectedDomain

-- Retargeted LPq_CarrierFacts
set_option autoImplicit false
namespace AspisR1.NGU_LPq_CarrierFacts
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_Carriers

theorem back_claim (x : NE) : NGU_LPq_ReadPorts.backE (NGU_Powers.claim x)=x := rfl

theorem weights_from_powers (gamma : NE) (hc : canonE gamma) (g : Array NE 29#usize)
    (call : FIo_Native.weights.powers 29#usize gamma=ok g) :
    NGU_LPq_ReadPorts.WeightsCanonical (arr NGU_Powers.claim g) := by
  have canonical := NGU_LPq_OutputDomains.powers gamma hc g call
  intro v hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
  rw [back_claim]
  exact canonical x hx

theorem native_unique {H : Type} (inst : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
    {sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize}
    {inactive kappa left right : NE} (hi : canonE inactive) (hk : canonE kappa)
    (lt : NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa left)
    (rt : NGU_LPq_PreparedTrace.Trace sem y1 g inactive kappa right) : left=right := by
  have same := NGU_LPq_PreparedClaim.uniqueness inst hi hk lt rt
  have port := congrArg NGU_LPq_ReadPorts.backE same
  simpa only [back_claim] using port

#print axioms back_claim
#print axioms weights_from_powers
#print axioms native_unique
end AspisR1.NGU_LPq_CarrierFacts

-- Retargeted LPr_WordValue
set_option autoImplicit false
namespace AspisR1.NGU_LPr_WordValue
open Aeneas Aeneas.Std

/-- Four arbitrary native bytes; no canonical-field or decoder-success premise. -/
theorem bits (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv =
      d.bv ++ c.bv ++ b.bv ++ a.bv := by
  change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv] : BitVec 32) = _
  ext i hi
  have bound : i < 32 := by simpa using hi
  rw [BitVec.fromLEBytes_getElem]
  rw [BitVec.getElem_append (by omega)]
  interval_cases i <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, ↓reduceDIte, Nat.reduceSub]
  all_goals try rw [BitVec.getElem_append (by omega)]
  all_goals try simp only [Nat.reduceLT, ↓reduceDIte, Nat.reduceSub]
  all_goals try rw [BitVec.getElem_append (by omega)]
  all_goals try simp only [Nat.reduceLT, ↓reduceDIte, Nat.reduceSub]
  all_goals rfl

#print axioms bits
end AspisR1.NGU_LPr_WordValue

-- Retargeted LPr_WordNat
set_option autoImplicit false
namespace AspisR1.NGU_LPr_WordNat
open Aeneas Aeneas.Std

theorem append_value {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2^n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- Natural little-endian formula for the exact native library decoder. -/
theorem value (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val =
      a.val + 256*b.val + 65536*c.val + 16777216*d.val := by
  change ((core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv).toNat = _
  rw [NGU_LPr_WordValue.bits, append_value, append_value, append_value]
  change ((d.val * 256 + c.val) * 256 + b.val) * 256 + a.val = _
  omega

#print axioms append_value
#print axioms value
end AspisR1.NGU_LPr_WordNat

-- Retargeted LPr_SelectedBytes
set_option autoImplicit false
namespace AspisR1.NGU_LPr_SelectedBytes
open Aeneas Aeneas.Std Result

/-- The actual bounded source index expression, on the SAME expanded carrier. -/
theorem selected (y1 : Slice U8) (len : y1.val.length=928)
    (l : Usize) (live : l.val<29) :
    ∃ b : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
        {start:=Usize.wrapping_mul l 32#usize,
         «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}=ok b ∧
      b.val.length=32 ∧ b.val=(y1.val.drop (32*l.val)).take 32 := by
  have add : (Usize.wrapping_add l 1#usize).val=l.val+1 := by
    rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt (by simp only [UScalar.size,UScalarTy.numBits,Usize.numBits]; scalar_tac)]
    rfl
  have start : (Usize.wrapping_mul l 32#usize).val=32*l.val := by
    rw [Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt (by simp only [UScalar.size,UScalarTy.numBits,Usize.numBits]; scalar_tac)]
    simp only [UScalar.ofNatCore_val_eq]; omega
  have finish : (Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize).val=32*(l.val+1) := by
    rw [Usize.wrapping_mul_val_eq, add, Nat.mod_eq_of_lt (by simp only [UScalar.size,UScalarTy.numBits,Usize.numBits]; scalar_tac)]
    simp only [UScalar.ofNatCore_val_eq]; omega
  let r : core.ops.range.Range Usize :=
    {start:=Usize.wrapping_mul l 32#usize,
     «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}
  have lo : r.start≤r.end := by simp only [r,UScalar.le_equiv,start,finish]; omega
  have hi : r.end≤y1.length := by simp only [r,UScalar.le_equiv,finish,Slice.length,len]; omega
  obtain ⟨b,run,bytes,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec r y1 lo hi)
  refine ⟨b,run,?_,?_⟩
  · simp only [Slice.length,r,start,finish] at size
    omega
  · simpa only [r,start,finish,List.slice,Nat.mul_add,Nat.mul_one,
      Nat.add_sub_cancel_left,Nat.add_sub_cancel] using bytes

#print axioms selected
end AspisR1.NGU_LPr_SelectedBytes

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
