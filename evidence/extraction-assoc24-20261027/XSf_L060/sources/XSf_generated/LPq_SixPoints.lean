import LPq_ReadPorts
set_option autoImplicit false
namespace AspisR1.LPq_SixPoints
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort AspisR1CurrentPreparedClaim

/-- Explicit remaining decoder-success domain. This is a local byte-read
observation, not a supplied public sum or whole-loop Result. Its establishment
from canonical_scan/expand_values is a separate caller obligation. -/
def SelectedFields (y1 : Slice U8) : Prop := ∀ l : Usize, l.val<29 →
  ∃ v : NE, canonE v ∧ FIo_Native.weights.field y1 l=ok v

theorem selected {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (hy : SelectedFields y1) (point l : Usize) (hp : point.val=5) (hl : l.val<29) :
    ∃ q : NQ, canonQ q ∧ ClaimScalar.read LPm_PointLoop.ops sem y1 point l=ok (qPort q) := by
  obtain ⟨v,cv,read⟩ := hy l hl
  have port := LPq_Decoder.claim_field y1 l hl
  rw [read] at port
  have hlarge : ¬ point≤2#usize := by scalar_tac
  refine ⟨v.c0,cv.1,?_⟩
  simp only [ClaimScalar.read,if_neg hlarge,hp]
  change (do let e ← ClaimParser.field y1 l; ClaimParser.c0 e)=ok (qPort v.c0)
  rw [←port]
  rfl

theorem domain {H : Type} (sem : r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : LPq_ReadPorts.WeightsCanonical g)
    (point : Usize) (hp : point.val<6) : LPq_PointConstruct.ReadDomain sem y1 g point := by
  by_cases h5 : point.val<5
  · exact LPq_ReadPorts.five_domains sem hs y1 g hg point h5
  · exact ⟨fun l hl => selected sem y1 hy point l (by omega) hl,
      fun l hl => LPq_ReadPorts.weights g hg l hl⟩

/-- All six linked native traces exist on ONE sem/y1/g carrier. Their 29-step
lengths and cohort loop Results follow from the retained LPm association. -/
theorem construct {H : Type} (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : LPq_ReadPorts.WeightsCanonical g)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val) :
    ∃ xs : Fin 6 → List (NE×NQ), ∃ out : Fin 6 → NE,
      (∀ i, LPm_PointLoop.Trace sem y1 g (point i)
        {start:=0#usize,«end»:=29#usize} LPm_PublicTwentyNine.zero (xs i) (out i)) ∧
      (∀ i, (xs i).length=29 ∧
        verifier.prepared_claim_dot_loop LPm_PointLoop.ops inst
          {start:=0#usize,«end»:=29#usize} sem y1 g (point i)
          (statePort LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i)))) := by
  have ex : ∀ i : Fin 6, ∃ xs out, LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize,«end»:=29#usize} LPm_PublicTwentyNine.zero xs out := by
    intro i
    exact LPq_PointConstruct.from_zero sem y1 g (point i)
      (domain sem hs y1 hy g hg (point i) (by rw [number]; exact i.isLt))
  choose xs out tr using ex
  refine ⟨xs,out,tr,?_⟩
  intro i
  have h := LPm_PointLength.all_six inst sem y1 g point number xs out tr i
  exact ⟨h.1,h.2.2.1⟩

#print axioms selected
#print axioms domain
#print axioms construct
end AspisR1.LPq_SixPoints
