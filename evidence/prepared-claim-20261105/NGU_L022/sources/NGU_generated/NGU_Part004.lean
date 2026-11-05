import Lean
import NGU_Part003
import NGU_ArrayRead
import NGU_Carriers
import NGU_ResultTransport
-- Retargeted LPm_PointLoop
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PointLoop
open Aeneas Aeneas.Std Result ControlFlow NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim
abbrev ops := AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw
abbrev Range := core.ops.range.Range Usize

/-- Linked local observations of the actual scalar loop. The read and weight
ports identify the caller's arguments; no loop Result or sum is assumed. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (point : Usize) :
    Range → Native → List (NE×NQ) → NE → Prop where
  | done (iter iter' : Range) (s : Native) (out : NE)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (none,iter'))
      (finish : FIo_Native.fast_pairing.EbyKDot.finish s=ok out) :
      Trace sem y1 g point iter s [] out
  | step {iter iter' : Range} {s s' : Native} {out : NE} {xs : List (NE×NQ)}
      (l : Usize) (v : NE) (q : NQ)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some l,iter'))
      (read : ClaimScalar.read ops sem y1 point l=ok (qPort q))
      (weight : Array.index_usize g l=ok (ePort v))
      (cv : canonE v) (cq : canonQ q) (count : s.count.val<29)
      (push : FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),s'))
      (tail : Trace sem y1 g point iter' s' xs out) :
      Trace sem y1 g point iter s ((v,q)::xs) out

theorem model_push (s s' : Native) (v : NE) (q : NQ)
    (cv : canonE v) (cq : canonQ q) (count : s.count.val<29)
    (push : FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),s')) :
    ops.pushDot (statePort s) (ePort v) (qPort q)=ok (.Ok (),statePort s') := by
  obtain ⟨actual,native,model⟩ := NGU_LPm_PublicPort.source s v q cv cq (by omega)
  have same : actual=s' := congrArg Prod.snd (Result.ok.inj (native.symm.trans push))
  subst actual
  exact model

theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {point : Usize} {iter : Range} {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : Trace sem y1 g point iter s xs out) :
    verifier.prepared_claim_dot_loop ops inst iter sem y1 g point (statePort s)=
      ok (.Ok (ePort out)) := by
  induction tr with
  | done iter iter' s out next finish =>
    obtain ⟨actual,native,model⟩ := NGU_LPm_FinishPort.source s
    have same := Result.ok.inj (native.symm.trans finish)
    subst actual
    have body : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point (statePort s)=
        ok (ControlFlow.done (.Ok (ePort out))) := by
      rw [ClaimScalar.body_eq_source]
      simp only [ClaimScalar.body,next,bind_tc_ok,model]
    change Aeneas.Std.loop _ _ = _
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    have model := model_push s s' v q cv cq count push
    have body : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point (statePort s)=
        ok (ControlFlow.cont (iter',sem,point,statePort s')) := by
      rw [ClaimScalar.body_eq_source]
      simp only [ClaimScalar.body,next,bind_tc_ok,read,weight,model,
        core.result.Result.map_err,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch]
    change Aeneas.Std.loop _ _ = _
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
    exact ih

#print axioms model_push
#print axioms source
end AspisR1.NGU_LPm_PointLoop

-- Retargeted LPm_SixPoints
set_option autoImplicit false
namespace AspisR1.NGU_LPm_SixPoints
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

theorem erase {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {point : Usize} {iter : NGU_LPm_PointLoop.Range}
    {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : NGU_LPm_PointLoop.Trace sem y1 g point iter s xs out) :
    ∃ last, NGU_LPm_PublicFold.Trace xs s last ∧
      FIo_Native.fast_pairing.EbyKDot.finish last=ok out := by
  induction tr with
  | done iter iter' s out next finish => exact ⟨s,.done s,finish⟩
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    obtain ⟨last,steps,finish⟩ := ih
    exact ⟨last,.step cv cq push steps,finish⟩

/-- All six point folds share the SAME caller sem/y1/g. The full cohort loop
Result and its 29-step field sum follow from linked local native transitions.
This theorem does not supply the missing native whole prepared_claim join. -/
theorem all_six {H : Type} (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val)
    (xs : Fin 6 → List (NE×NQ)) (out : Fin 6 → NE)
    (size : ∀ i, (xs i).length=29)
    (tr : ∀ i, NGU_LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize, «end»:=29#usize} NGU_LPm_PublicTwentyNine.zero (xs i) (out i)) :
    ∀ i, (point i).val<6 ∧
      verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst
        {start:=0#usize, «end»:=29#usize} sem y1 g (point i)
        (statePort NGU_LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i))) ∧
      ∃ last, NGU_LPm_PublicFold.Bounded last 29 ∧
        NGU_LPm_PublicFold.meaning last=NGU_LPm_PublicFold.fold
          (NGU_LPm_PublicFold.meaning NGU_LPm_PublicTwentyNine.zero) (xs i) ∧
        FIo_Native.fast_pairing.EbyKDot.finish last=ok (out i) := by
  intro i
  obtain ⟨last,steps,finish⟩ := erase (tr i)
  obtain ⟨bound,value⟩ := NGU_LPm_PublicTwentyNine.source (xs i) last (size i) steps
  exact ⟨by rw [number]; exact i.isLt,
    NGU_LPm_PointLoop.source inst (tr i),last,bound,value,finish⟩

#print axioms erase
#print axioms all_six
end AspisR1.NGU_LPm_SixPoints

-- Retargeted LPm_PointLength
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PointLength
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

theorem length {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {point : Usize} {iter : NGU_LPm_PointLoop.Range}
    {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : NGU_LPm_PointLoop.Trace sem y1 g point iter s xs out)
    (last : iter.end.val=29) (bound : iter.start.val≤29) :
    xs.length=29-iter.start.val := by
  induction tr with
  | done iter iter' s out next finish =>
    have h := ClaimTrace.next_none_bound iter iter' next
    simp only [List.length_nil]
    omega
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    obtain ⟨hl,active,start,finish⟩ := ClaimTrace.next_some_step iter iter' l next
    have e : iter'.end.val=29 := by rw [finish]; exact last
    have b : iter'.start.val≤29 := by omega
    have n := ih e b
    simp only [List.length_cons]
    omega

/-- The actual iterator observations determine every one of the six fold
lengths. No supplied length, public sum, or whole-loop equality is required. -/
theorem all_six {H : Type} (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val)
    (xs : Fin 6 → List (NE×NQ)) (out : Fin 6 → NE)
    (tr : ∀ i, NGU_LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize, «end»:=29#usize} NGU_LPm_PublicTwentyNine.zero (xs i) (out i)) :
    ∀ i, (xs i).length=29 ∧ (point i).val<6 ∧
      verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst
        {start:=0#usize, «end»:=29#usize} sem y1 g (point i)
        (statePort NGU_LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i))) ∧
      ∃ last, NGU_LPm_PublicFold.Bounded last 29 ∧
        NGU_LPm_PublicFold.meaning last=NGU_LPm_PublicFold.fold
          (NGU_LPm_PublicFold.meaning NGU_LPm_PublicTwentyNine.zero) (xs i) ∧
        FIo_Native.fast_pairing.EbyKDot.finish last=ok (out i) := by
  have sizes : ∀ i, (xs i).length=29 := by
    intro i
    have h := length (tr i) rfl (by decide)
    change (xs i).length=29-0 at h
    exact h
  intro i
  exact ⟨sizes i,NGU_LPm_SixPoints.all_six inst sem y1 g point number xs out sizes tr i⟩

#print axioms length
#print axioms all_six
end AspisR1.NGU_LPm_PointLength

-- Retargeted LPq_PointConstruct
set_option autoImplicit false
namespace AspisR1.NGU_LPq_PointConstruct
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

/-- Local read ports, not a supplied loop trace or output equation. The concrete
semantic and selected-byte decoder domain must establish these ports. -/
def ReadDomain {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (point : Usize) : Prop :=
  (∀ l : Usize, l.val<29 → ∃ q : NQ, canonQ q ∧
    ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point l=ok (qPort q)) ∧
  (∀ l : Usize, l.val<29 → ∃ v : NE, canonE v ∧
    Array.index_usize g l=ok (ePort v))

/-- Construct the linked native observations by induction on remaining source
iterations. Nothing assumes a complete public-fold trace or whole-loop Result. -/
theorem loop {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (point : Usize)
    (domain : ReadDomain sem y1 g point) (fuel : Nat)
    (iter : NGU_LPm_PointLoop.Range) (s : Native)
    (last : iter.end.val=29) (bound : iter.start.val≤29)
    (remaining : 29-iter.start.val≤fuel)
    (bounded : NGU_LPm_PublicFold.Bounded s iter.start.val) :
    ∃ xs out, NGU_LPm_PointLoop.Trace sem y1 g point iter s xs out := by
  induction fuel generalizing iter s with
  | zero =>
    have stopped : ¬ (iter.start.val < iter.end.val) := by omega
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter)
    simp only [stopped,↓reduceIte] at shape
    obtain ⟨out,finish,_⟩ := NGU_LPm_FinishPort.source s
    exact ⟨[],out,.done iter iter' s out (by rw [shape.1.1] at call; exact call) finish⟩
  | succ n ih =>
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter)
    by_cases active : iter.start.val < iter.end.val
    · simp only [active,↓reduceIte] at shape
      have hl : iter.start.val<29 := by omega
      obtain ⟨q,cq,read⟩ := domain.1 iter.start hl
      obtain ⟨v,cv,weight⟩ := domain.2 iter.start hl
      obtain ⟨next,push,bnext,_⟩ := NGU_LPm_PublicFold.step s v q iter.start.val hl bounded cv cq
      have last' : iter'.end.val=29 := by rw [shape.2]; exact last
      have advance : iter'.start.val=iter.start.val+1 := shape.1.2
      have bound' : iter'.start.val≤29 := by omega
      have remain' : 29-iter'.start.val≤n := by omega
      have bn : NGU_LPm_PublicFold.Bounded next iter'.start.val := by rw [shape.1.2]; exact bnext
      obtain ⟨xs,out,tail⟩ := ih iter' next last' bound' remain' bn
      exact ⟨(v,q)::xs,out,.step iter.start v q
        (by rw [shape.1.1] at call; exact call) read weight cv cq
        (by rw [bounded.1]; exact hl) push tail⟩
    · simp only [active,↓reduceIte] at shape
      obtain ⟨out,finish,_⟩ := NGU_LPm_FinishPort.source s
      exact ⟨[],out,.done iter iter' s out (by rw [shape.1.1] at call; exact call) finish⟩

theorem from_zero {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (point : Usize)
    (domain : ReadDomain sem y1 g point) :
    ∃ xs out, NGU_LPm_PointLoop.Trace sem y1 g point
      {start:=0#usize,«end»:=29#usize} NGU_LPm_PublicTwentyNine.zero xs out := by
  exact loop sem y1 g point domain 29 _ _ rfl (by decide) (by decide)
    NGU_LPm_PublicTwentyNine.initial_bound

#print axioms loop
#print axioms from_zero
end AspisR1.NGU_LPq_PointConstruct

-- Retargeted LPq_IndexPorts
set_option autoImplicit false
namespace AspisR1.NGU_LPq_IndexPorts
open Aeneas Aeneas.Std Result

theorem add (x y : Usize) (h : x.val+y.val<UScalar.size .Usize) :
    x+y=ok (Usize.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by
    have hm : x.val+y.val ≤ Usize.max := by
      simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at h ⊢
      scalar_tac
    simpa only [UScalar.max_USize_eq] using hm))
  have hw := Usize.wrapping_add_val_eq x y
  rw [Nat.mod_eq_of_lt h] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

theorem mul (x y : Usize) (h : x.val*y.val<UScalar.size .Usize) :
    x*y=ok (Usize.wrapping_mul x y) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) (by
    have hm : x.val*y.val ≤ Usize.max := by
      simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at h ⊢
      scalar_tac
    simpa only [UScalar.max_USize_eq] using hm))
  have hw := Usize.wrapping_mul_val_eq x y
  rw [Nat.mod_eq_of_lt h] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

#print axioms add
#print axioms mul
end AspisR1.NGU_LPq_IndexPorts

-- Retargeted LPq_Decoder
set_option autoImplicit false
namespace AspisR1.NGU_LPq_Decoder
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_Carriers NGU_ResultTransport

def record (x : NE) : AspisR1RecordParser.field.wide_exact.WideExact :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem limbs (a : Array U32 8#usize) :
    mapR (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a)=
      AspisR1RecordParser.field.wide_exact.WideExact.from_limbs a := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
    FIo_Native.aspis_core.field.P,AspisR1RecordParser.field.P,
    mapR_bind,map_if,map_ok,Option.map_some,Option.map_none,record]

theorem bytes (b : Slice U8) :
    mapR (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b)=
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN,
    map_if,map_ok,Option.map_none,mapR_bind,limbs]

theorem unwrap (o : Option NE) :
    mapR record (core.option.Option.unwrap o)=core.option.Option.unwrap (Option.map record o) := by
  cases o <;> rfl

theorem field (b : Slice U8) (i : Usize) (hi : i.val<29) :
    mapR record (FIo_Native.weights.field b i)=
      AspisR1WeightsFieldCurrent.weights.field
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b i := by
  have hm : 928<UScalar.size .Usize := by
    have hmax : 928 ≤ Usize.max := by scalar_tac
    simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at hmax ⊢
    scalar_tac
  have h32 : (32#usize).val=32 := by scalar_tac
  have h1 : (1#usize).val=1 := by scalar_tac
  have fitsAdd : i.val+(1#usize).val<UScalar.size .Usize := by rw [h1]; omega
  have nextVal : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
    rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt fitsAdd,h1]
  have rm := NGU_LPq_IndexPorts.mul i 32#usize (by rw [h32]; omega)
  have ra := NGU_LPq_IndexPorts.add i 1#usize fitsAdd
  have re := NGU_LPq_IndexPorts.mul (Usize.wrapping_add i 1#usize) 32#usize
    (by rw [nextVal,h32]; omega)
  unfold FIo_Native.weights.field AspisR1WeightsFieldCurrent.weights.field
  simp only [mapR_bind,←bytes,bind_map,unwrap,rm,ra,re,lift,bind_tc_ok]

/-- SAME selected-byte parser, full Result including noncanonical and range
failures, after the concrete eight-word cohort owner port. -/
theorem claim_field (b : Slice U8) (i : Usize) (hi : i.val<29) :
    mapR NGU_Powers.claim (FIo_Native.weights.field b i)=
      AspisR1CurrentPreparedClaim.ClaimParser.field b i := by
  unfold AspisR1CurrentPreparedClaim.ClaimParser.field AspisR1CurrentWide.Proof.finishField
  rw [←field b i hi]
  simp only [mapR,bind_assoc_eq,bind_tc_ok]
  rfl

#print axioms limbs
#print axioms bytes
#print axioms unwrap
#print axioms field
#print axioms claim_field
end AspisR1.NGU_LPq_Decoder

-- Retargeted LPq_ReadPorts
set_option autoImplicit false
namespace AspisR1.NGU_LPq_ReadPorts
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

def backQ (q : aspis_core.field.QM31) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def backE (e : Concrete.E) : NE := ⟨backQ e.c0,backQ e.c1⟩
theorem q_roundtrip (q : aspis_core.field.QM31) : qPort (backQ q)=q := rfl
theorem e_roundtrip (e : Concrete.E) : ePort (backE e)=e := rfl

def SemCanonical {H : Type} (sem : r1_semantic.Verified H) : Prop :=
  (∀ row ∈ sem.claims.val, ∀ q ∈ row.val, canonQ (backQ q)) ∧
  (∀ q ∈ sem.extra.val, canonQ (backQ q)) ∧
  (∀ q ∈ sem.before_z1.val, canonQ (backQ q))

def WeightsCanonical (g : Array Concrete.E 29#usize) : Prop :=
  ∀ v ∈ g.val, canonE (backE v)

theorem weights (g : Array Concrete.E 29#usize) (hg : WeightsCanonical g)
    (l : Usize) (hl : l.val<29) :
    ∃ v : NE, canonE v ∧ Array.index_usize g l=ok (ePort v) := by
  have h : l.val<g.val.length := by rw [g.property]; exact hl
  exact ⟨backE g.val[l.val],hg _ (List.getElem_mem h),by
    rw [e_roundtrip]; exact NGU_ArrayRead.read g l hl⟩

/-- Selection ports derived from the SAME semantic arrays, not supplied reads. -/
theorem semantic {H : Type} (sem : r1_semantic.Verified H) (hc : SemCanonical sem)
    (y1 : Slice U8) (point l : Usize) (hp : point.val<5) (hl : l.val<29) :
    ∃ q : NQ, canonQ q ∧ ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point l=ok (qPort q) := by
  by_cases h3 : point.val<3
  · have pr : point.val<sem.claims.val.length := by rw [sem.claims.property]; exact h3
    let row := sem.claims.val[point.val]
    have lr : l.val<row.val.length := by rw [row.property]; exact hl
    refine ⟨backQ row.val[l.val],hc.1 _ (List.getElem_mem pr) _ (List.getElem_mem lr),?_⟩
    rw [q_roundtrip,NGU_LPm_SemanticSelections.claims _ _ _ _ _ h3,
      NGU_ArrayRead.read sem.claims point h3,bind_tc_ok]
    exact NGU_ArrayRead.read row l hl
  · by_cases h4 : point.val=3
    · have lr : l.val<sem.extra.val.length := by rw [sem.extra.property]; exact hl
      refine ⟨backQ sem.extra.val[l.val],hc.2.1 _ (List.getElem_mem lr),?_⟩
      rw [q_roundtrip,NGU_LPm_SemanticSelections.extra _ _ _ _ _ h4]
      exact NGU_ArrayRead.read sem.extra l hl
    · have h5 : point.val=4 := by omega
      have lr : l.val<sem.before_z1.val.length := by rw [sem.before_z1.property]; exact hl
      refine ⟨backQ sem.before_z1.val[l.val],hc.2.2 _ (List.getElem_mem lr),?_⟩
      rw [q_roundtrip,NGU_LPm_SemanticSelections.before_z1 _ _ _ _ _ h5]
      exact NGU_ArrayRead.read sem.before_z1 l hl

theorem five_domains {H : Type} (sem : r1_semantic.Verified H) (hc : SemCanonical sem)
    (y1 : Slice U8) (g : Array Concrete.E 29#usize) (hg : WeightsCanonical g)
    (point : Usize) (hp : point.val<5) : NGU_LPq_PointConstruct.ReadDomain sem y1 g point :=
  ⟨fun l hl => semantic sem hc y1 point l hp hl, fun l hl => weights g hg l hl⟩

#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms weights
#print axioms semantic
#print axioms five_domains
end AspisR1.NGU_LPq_ReadPorts

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
