import Lean
import NGU_Part004
import NFU_LPl_Check
import NFU_LPn_ExpandTrace
import NGU_Weighted
import NFW_LPm_PowersBridge
-- Retargeted LPq_SixPoints
set_option autoImplicit false
namespace AspisR1.NGU_LPq_SixPoints
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort AspisR1CurrentPreparedClaim

/-- Explicit remaining decoder-success domain. This is a local byte-read
observation, not a supplied public sum or whole-loop Result. Its establishment
from canonical_scan/expand_values is a separate caller obligation. -/
def SelectedFields (y1 : Slice U8) : Prop := ∀ l : Usize, l.val<29 →
  ∃ v : NE, canonE v ∧ FIo_Native.weights.field y1 l=ok v

theorem selected {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (hy : SelectedFields y1) (point l : Usize) (hp : point.val=5) (hl : l.val<29) :
    ∃ q : NQ, canonQ q ∧ ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point l=ok (qPort q) := by
  obtain ⟨v,cv,read⟩ := hy l hl
  have port := NGU_LPq_Decoder.claim_field y1 l hl
  rw [read] at port
  have hlarge : ¬ point≤2#usize := by scalar_tac
  refine ⟨v.c0,cv.1,?_⟩
  simp only [ClaimScalar.read,if_neg hlarge,hp]
  change (do let e ← ClaimParser.field y1 l; ClaimParser.c0 e)=ok (qPort v.c0)
  rw [←port]
  rfl

theorem domain {H : Type} (sem : r1_semantic.Verified H)
    (hs : NGU_LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : NGU_LPq_ReadPorts.WeightsCanonical g)
    (point : Usize) (hp : point.val<6) : NGU_LPq_PointConstruct.ReadDomain sem y1 g point := by
  by_cases h5 : point.val<5
  · exact NGU_LPq_ReadPorts.five_domains sem hs y1 g hg point h5
  · exact ⟨fun l hl => selected sem y1 hy point l (by omega) hl,
      fun l hl => NGU_LPq_ReadPorts.weights g hg l hl⟩

/-- All six linked native traces exist on ONE sem/y1/g carrier. Their 29-step
lengths and cohort loop Results follow from the retained LPm association. -/
theorem construct {H : Type} (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (hs : NGU_LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : NGU_LPq_ReadPorts.WeightsCanonical g)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val) :
    ∃ xs : Fin 6 → List (NE×NQ), ∃ out : Fin 6 → NE,
      (∀ i, NGU_LPm_PointLoop.Trace sem y1 g (point i)
        {start:=0#usize,«end»:=29#usize} NGU_LPm_PublicTwentyNine.zero (xs i) (out i)) ∧
      (∀ i, (xs i).length=29 ∧
        verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst
          {start:=0#usize,«end»:=29#usize} sem y1 g (point i)
          (statePort NGU_LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i)))) := by
  have ex : ∀ i : Fin 6, ∃ xs out, NGU_LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize,«end»:=29#usize} NGU_LPm_PublicTwentyNine.zero xs out := by
    intro i
    exact NGU_LPq_PointConstruct.from_zero sem y1 g (point i)
      (domain sem hs y1 hy g hg (point i) (by rw [number]; exact i.isLt))
  choose xs out tr using ex
  refine ⟨xs,out,tr,?_⟩
  intro i
  have h := NGU_LPm_PointLength.all_six inst sem y1 g point number xs out tr i
  exact ⟨h.1,h.2.2.1⟩

#print axioms selected
#print axioms domain
#print axioms construct
end AspisR1.NGU_LPq_SixPoints

-- Retargeted LPt_LPs_CheckDomain
set_option autoImplicit false
namespace AspisR1.NGU_LPt_LPs_CheckDomain
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : Nat := (bs[i]?.getD 0#u8).val
def word (bs : List U8) (i : Nat) : Nat :=
  byte bs i + 256*byte bs (i+1) + 65536*byte bs (i+2) + 16777216*byte bs (i+3)
def CompactCanonical (bs : List U8) : Prop := ∀ row, row<29 → ∀ limb,
  limb<4 → word bs (16*row+4*limb)<2147483647

theorem byte_window (bs : List U8) (off width j : Nat) (hj : j<width) :
    byte ((bs.drop off).take width) j=byte bs (off+j) := by
  simp only [byte,List.getElem?_take,hj,↓reduceIte,List.getElem?_drop]

theorem word_window (bs : List U8) (off width j : Nat) (hj : j+3<width) :
    word ((bs.drop off).take width) j=word bs (off+j) := by
  simp only [word,byte_window bs off width j (by omega),
    byte_window bs off width (j+1) (by omega),
    byte_window bs off width (j+2) (by omega),
    byte_window bs off width (j+3) hj,Nat.add_assoc]

theorem echeck_word (bs : List U8) : NFU_Retarget.LPl.Echeck.word bs=word bs 0 := by
  simp only [NFU_Retarget.LPl.Echeck.word,NFU_Retarget.LPl.Echeck.byte,word,byte,
    Nat.zero_add,Nat.mul_add]
  omega

theorem checked (compact : Slice U8) (len : compact.val.length=464)
    (success : _root_.NFU_Retarget.compact.check_values compact=ok (.Ok ())) :
    CompactCanonical compact.val := by
  obtain ⟨out,trace⟩ := NFU_Retarget.LPl.Check.total compact.val
  have call := NFU_Retarget.LPl.Check.native_result compact out trace
  have none : out=none := by
    cases out <;> simp_all
  subst out
  have hit := NFU_Retarget.LPl.Scan.first_error _ _ _ trace
  have good := (NFU_Retarget.LPl_A.firstBad_none _ _).mp hit.symm
  intro row hr limb hl
  have count : row<compact.val.length/16 := by omega
  have row_good := good row count
  have chunk : NFU_Retarget.LPl.Check.chunk ((compact.val.drop (16*row)).take 16)=true := by
    change (!NFU_Retarget.LPl.Check.chunk _)=false at row_good
    cases h : NFU_Retarget.LPl.Check.chunk ((compact.val.drop (16*row)).take 16) <;> simp_all
  have limbs := List.all_eq_true.mp chunk
  have bound := limbs limb (List.mem_range.mpr hl)
  change decide (NFU_Retarget.LPl.Echeck.word _ < 2147483647)=true at bound
  have bound' := of_decide_eq_true bound
  rw [echeck_word,word_window _ (4*limb) 4 0 (by omega),Nat.add_zero,
    word_window _ (16*row) 16 (4*limb) (by omega)] at bound'
  exact bound'

#print axioms byte_window
#print axioms word_window
#print axioms echeck_word
#print axioms checked
end AspisR1.NGU_LPt_LPs_CheckDomain

-- Retargeted LPt_LPs_ExpandDomain
set_option autoImplicit false
namespace AspisR1.NGU_LPt_LPs_ExpandDomain
open Aeneas Aeneas.Std Result NGU_LPt_LPs_CheckDomain

def Expanded (compact y1 : List U8) : Prop := ∀ row, row<29 → ∀ lane, lane<32 →
  byte y1 (32*row+lane)=if lane<16 then byte compact (16*row+lane) else 0

theorem expanded (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (trace : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    y1.val.length=928 ∧ Expanded compact.val y1.val ∧
    _root_.NFU_Retarget.compact.expand_values compact before=ok (.Ok (),y1) := by
  have inherited := NFU_Retarget.LPn.Expand.to_inherited _ _ _ _ trace
  have length := NFU_Retarget.LPl.Expand.length _ _ _ _ inherited
  refine ⟨length.trans size,?_,?_⟩
  · intro row hr lane hl
    have observed := NFU_Retarget.LPl.Expand.invariant _ _ _ _ inherited (32*row+lane) (by omega)
    rw [if_pos (by omega)] at observed
    have div : (32*row+lane)/32=row := by omega
    have mod : (32*row+lane)%32=lane := by omega
    simp only [NFU_Retarget.LPl_A.Expand.byte,div,mod] at observed
    unfold byte
    rw [observed]
    split <;> (try simp only [Nat.mul_comm]) <;> rfl
  · apply NFU_Retarget.LPn.Expand.native_result compact before y1 (by omega) (by omega) (by omega)
    simpa only [len] using trace

#print axioms expanded
end AspisR1.NGU_LPt_LPs_ExpandDomain

-- Retargeted LPq_ExpandedWords
set_option autoImplicit false
namespace AspisR1.NGU_LPq_ExpandedWords
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : Nat := (bs[i]?.getD 0#u8).val
def word (bs : List U8) (i : Nat) : Nat :=
  byte bs i + 256*byte bs (i+1) + 65536*byte bs (i+2) + 16777216*byte bs (i+3)

/-- Exactly the low16-copy/high16-zero postcondition of the CLOSED LPn
expand_values leaf on the same compact and expanded carriers. -/
def Expanded (compact y1 : List U8) : Prop := ∀ row, row<29 → ∀ lane, lane<32 →
  byte y1 (32*row+lane)=if lane<16 then byte compact (16*row+lane) else 0

def CompactCanonical (compact : List U8) : Prop := ∀ row, row<29 → ∀ limb,
  limb<4 → word compact (16*row+4*limb)<2147483647

theorem low (compact y1 : List U8) (h : Expanded compact y1) (row limb : Nat)
    (hr : row<29) (hl : limb<4) :
    word y1 (32*row+4*limb)=word compact (16*row+4*limb) := by
  have b0 := h row hr (4*limb) (by omega)
  have b1 := h row hr (4*limb+1) (by omega)
  have b2 := h row hr (4*limb+2) (by omega)
  have b3 := h row hr (4*limb+3) (by omega)
  simp only [if_pos (show 4*limb<16 by omega)] at b0
  simp only [if_pos (show 4*limb+1<16 by omega)] at b1
  simp only [if_pos (show 4*limb+2<16 by omega)] at b2
  simp only [if_pos (show 4*limb+3<16 by omega)] at b3
  simp only [word,Nat.add_assoc,b0,b1,b2,b3]

theorem high (compact y1 : List U8) (h : Expanded compact y1) (row limb : Nat)
    (hr : row<29) (hl : 4≤limb) (hu : limb<8) : word y1 (32*row+4*limb)=0 := by
  have b0 := h row hr (4*limb) (by omega)
  have b1 := h row hr (4*limb+1) (by omega)
  have b2 := h row hr (4*limb+2) (by omega)
  have b3 := h row hr (4*limb+3) (by omega)
  simp only [if_neg (show ¬ (4*limb<16) by omega)] at b0
  simp only [if_neg (show ¬ (4*limb+1<16) by omega)] at b1
  simp only [if_neg (show ¬ (4*limb+2<16) by omega)] at b2
  simp only [if_neg (show ¬ (4*limb+3<16) by omega)] at b3
  simp only [word,Nat.add_assoc,b0,b1,b2,b3,Nat.mul_zero,Nat.add_zero]

theorem canonical (compact y1 : List U8) (h : Expanded compact y1)
    (hc : CompactCanonical compact) (row limb : Nat) (hr : row<29) (hl : limb<8) :
    word y1 (32*row+4*limb)<2147483647 := by
  by_cases small : limb<4
  · rw [low compact y1 h row limb hr small];exact hc row hr limb small
  · rw [high compact y1 h row limb hr (by omega) hl];decide

#print axioms low
#print axioms high
#print axioms canonical
end AspisR1.NGU_LPq_ExpandedWords

-- Retargeted LPq_DecodeTotal
set_option autoImplicit false
namespace AspisR1.NGU_LPq_DecodeTotal
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

theorem limbs (a : Array U32 8#usize)
    (hc : ∀ i, ∀ h : i<a.val.length, (a.val[i]'h).val<2147483647) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a=ok (some out) ∧ canonE out := by
  have len : a.val.length=8 := a.property
  have r0 := NGU_ArrayRead.read a 0#usize (by decide)
  have c0 := hc 0 (by omega)
  have g0 : ¬ a.val[0] ≥ 2147483647#u32 := by scalar_tac
  have r1 := NGU_ArrayRead.read a 1#usize (by decide)
  have c1 := hc 1 (by omega)
  have g1 : ¬ a.val[1] ≥ 2147483647#u32 := by scalar_tac
  have r2 := NGU_ArrayRead.read a 2#usize (by decide)
  have c2 := hc 2 (by omega)
  have g2 : ¬ a.val[2] ≥ 2147483647#u32 := by scalar_tac
  have r3 := NGU_ArrayRead.read a 3#usize (by decide)
  have c3 := hc 3 (by omega)
  have g3 : ¬ a.val[3] ≥ 2147483647#u32 := by scalar_tac
  have r4 := NGU_ArrayRead.read a 4#usize (by decide)
  have c4 := hc 4 (by omega)
  have g4 : ¬ a.val[4] ≥ 2147483647#u32 := by scalar_tac
  have r5 := NGU_ArrayRead.read a 5#usize (by decide)
  have c5 := hc 5 (by omega)
  have g5 : ¬ a.val[5] ≥ 2147483647#u32 := by scalar_tac
  have r6 := NGU_ArrayRead.read a 6#usize (by decide)
  have c6 := hc 6 (by omega)
  have g6 : ¬ a.val[6] ≥ 2147483647#u32 := by scalar_tac
  have r7 := NGU_ArrayRead.read a 7#usize (by decide)
  have c7 := hc 7 (by omega)
  have g7 : ¬ a.val[7] ≥ 2147483647#u32 := by scalar_tac
  refine ⟨⟨⟨⟨a.val[0],a.val[1]⟩,⟨a.val[2],a.val[3]⟩⟩,⟨⟨a.val[4],a.val[5]⟩,⟨a.val[6],a.val[7]⟩⟩⟩,?_,⟨⟨⟨c0,c1⟩,⟨c2,c3⟩⟩,⟨⟨c4,c5⟩,⟨c6,c7⟩⟩⟩⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    FIo_Native.aspis_core.field.P,UScalar.ofNatCore_val_eq,bind_tc_ok,r0,g0,r1,g1,r2,g2,r3,g3,r4,g4,r5,g5,r6,g6,r7,g7,↓reduceIte]

#print axioms limbs
end AspisR1.NGU_LPq_DecodeTotal

-- Retargeted LPq_BytesTotal
set_option autoImplicit false
namespace AspisR1.NGU_LPq_BytesTotal
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

def byte (b : Slice U8) (i : Nat) : U8 := b.val[i]?.getD 0#u8
def word (b : Slice U8) (j : Nat) : U32 := core.num.U32.from_le_bytes
  (Array.make 4#usize [byte b (4*j),byte b (4*j+1),byte b (4*j+2),byte b (4*j+3)])

theorem read (b : Slice U8) (len : b.val.length=32) (i : Usize) (hi : i.val<32) :
    Slice.index_usize b i=ok (byte b i.val) := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i (by simpa only [Slice.length,len] using hi))
  rw [value] at run
  simpa only [byte,List.getElem?_eq_getElem (show i.val<b.val.length by omega),Option.getD_some] using run

theorem source (b : Slice U8) (len : b.val.length=32)
    (hc : ∀ j, j<8 → (word b j).val<2147483647) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b=ok (some out) ∧ canonE out := by
  let a : Array U32 8#usize := Array.make 8#usize [word b 0,word b 1,word b 2,word b 3,word b 4,word b 5,word b 6,word b 7]
  have ca : ∀ i, ∀ h : i<a.val.length, (a.val[i]'h).val<2147483647 := by
    intro i hi
    have bound : i<8 := by simpa only [a,Array.make,List.length_cons,List.length_nil] using hi
    interval_cases i
    · exact hc 0 (by decide)
    · exact hc 1 (by decide)
    · exact hc 2 (by decide)
    · exact hc 3 (by decide)
    · exact hc 4 (by decide)
    · exact hc 5 (by decide)
    · exact hc 6 (by decide)
    · exact hc 7 (by decide)
  obtain ⟨out,call,co⟩ := NGU_LPq_DecodeTotal.limbs a ca
  have hlen : Slice.len b=32#usize := by
    apply UScalar.eq_of_val_eq
    change b.val.length=_
    rw [len]
    rfl
  refine ⟨out,?_,co⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,hlen,bne_self_eq_false,↓reduceIte]
  have r0 := read b len 0#usize (by decide)
  have r1 := read b len 1#usize (by decide)
  have r2 := read b len 2#usize (by decide)
  have r3 := read b len 3#usize (by decide)
  have r4 := read b len 4#usize (by decide)
  have r5 := read b len 5#usize (by decide)
  have r6 := read b len 6#usize (by decide)
  have r7 := read b len 7#usize (by decide)
  have r8 := read b len 8#usize (by decide)
  have r9 := read b len 9#usize (by decide)
  have r10 := read b len 10#usize (by decide)
  have r11 := read b len 11#usize (by decide)
  have r12 := read b len 12#usize (by decide)
  have r13 := read b len 13#usize (by decide)
  have r14 := read b len 14#usize (by decide)
  have r15 := read b len 15#usize (by decide)
  have r16 := read b len 16#usize (by decide)
  have r17 := read b len 17#usize (by decide)
  have r18 := read b len 18#usize (by decide)
  have r19 := read b len 19#usize (by decide)
  have r20 := read b len 20#usize (by decide)
  have r21 := read b len 21#usize (by decide)
  have r22 := read b len 22#usize (by decide)
  have r23 := read b len 23#usize (by decide)
  have r24 := read b len 24#usize (by decide)
  have r25 := read b len 25#usize (by decide)
  have r26 := read b len 26#usize (by decide)
  have r27 := read b len 27#usize (by decide)
  have r28 := read b len 28#usize (by decide)
  have r29 := read b len 29#usize (by decide)
  have r30 := read b len 30#usize (by decide)
  have r31 := read b len 31#usize (by decide)
  simpa only [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,UScalar.ofNatCore_val_eq,bind_tc_ok,lift,word,byte,a,Bool.false_eq_true,if_false] using call

#print axioms read
#print axioms source
end AspisR1.NGU_LPq_BytesTotal

-- Retargeted LPq_OutputDomains
set_option autoImplicit false
namespace AspisR1.NGU_LPq_OutputDomains
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort

theorem finish (s : Native) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧ canonE out := by
  obtain ⟨out,run,h0,h1,h2,h3,h4,h5,h6,h7⟩ := NGU_LPf_PublicDotAllStates.source s
  refine ⟨out,run,?_⟩
  change ((out.c0.c0.a.val<2147483647 ∧ out.c0.c0.b.val<2147483647) ∧
    (out.c0.c1.a.val<2147483647 ∧ out.c0.c1.b.val<2147483647)) ∧
    ((out.c1.c0.a.val<2147483647 ∧ out.c1.c0.b.val<2147483647) ∧
    (out.c1.c1.a.val<2147483647 ∧ out.c1.c1.b.val<2147483647))
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  exact ⟨⟨⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩⟩,
    ⟨⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩⟩⟩

theorem point {H : Type} {sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H}
    {y1 : Slice U8} {g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize}
    {p : Usize} {iter : NGU_LPm_PointLoop.Range} {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : NGU_LPm_PointLoop.Trace sem y1 g p iter s xs out) : canonE out := by
  induction tr with
  | done iter iter' s out next run =>
    obtain ⟨actual,call,ca⟩ := finish s
    have same : actual=out := Result.ok.inj (call.symm.trans run)
    simpa only [same] using ca
  | step l v q next read weight cv cq count push tail ih => exact ih

theorem powers {N : Usize} (x : NE) (hx : canonE x) (a : Array NE N)
    (run : FIo_Native.weights.powers N x=ok a) : ∀ z ∈ a.val, canonE z := by
  obtain ⟨actual,call,holds⟩ := NFW_LPi_PowersSource.source N x hx
  have same : actual=a := Result.ok.inj (call.symm.trans run)
  subst actual
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hz
  have bound : i<N.val := by rw [←a.property]; exact hi
  obtain ⟨v,hv,cv,_⟩ := holds i bound
  rw [List.getElem?_eq_getElem hi] at hv
  exact (Option.some.inj hv) ▸ cv

#print axioms finish
#print axioms point
#print axioms powers
end AspisR1.NGU_LPq_OutputDomains

-- Retargeted LPq_ArrayPorts
set_option autoImplicit false
namespace AspisR1.NGU_LPq_ArrayPorts
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_Carriers

theorem update {A : Type} {N : Usize} (a : Array A N) (i : Usize) (v : A)
    (hi : i.val<N.val) : Array.update a i v=ok (a.set i v) := by
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists (Array.update_spec a i v (by simpa only [Array.length,a.property] using hi))
  exact call.trans (congrArg ok value)

theorem mapped {A B : Type} {N : Usize} (f : A → B) (a : Array A N)
    (i : Usize) (v : A) (hi : i.val<N.val) :
    Array.update (arr f a) i (f v)=ok (arr f (a.set i v)) := by
  rw [update _ _ _ hi,NGU_ArrayMap.set]

theorem canonical_set (a : NGU_WeightedStep.Seven) (i : Usize) (v : NE)
    (ha : NGU_WeightedStep.canonical a) (hv : canonE v) :
    NGU_WeightedStep.canonical (a.set i v) := by
  change ∀ z ∈ a.val.set i.val v, canonE z
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hz
  rw [List.getElem_set]
  split
  · exact hv
  · exact ha _ (List.getElem_mem _)

#print axioms update
#print axioms mapped
#print axioms canonical_set
end AspisR1.NGU_LPq_ArrayPorts

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
