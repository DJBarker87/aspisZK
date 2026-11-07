import LIB_VRecordsAll
set_option autoImplicit false
noncomputable section
namespace LIB_VClaimsCanonical
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 ClaimsUnrolledFinish
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter (decodeMain_success_members_canonical)
def AllRows (a : AspisR1ClaimsUnrolledParent.Claims) : Prop :=
 ∀ row∈a.val,LIB_VArray.Canonical (toMainArray row)
theorem array_back {n : Usize} (a : Array MainQM n) : toMainArray (fromMainArray a) = a := by
 apply Subtype.ext
 simp only [toMainArray,fromMainArray,List.map_map,Function.comp_def]
 have inverse : ∀ q : MainQM,toMainQM (fromMainQM q)=q := fun _=>rfl
 simp only [inverse]
 exact List.map_id a.val
theorem source_canonical (n : Usize) (r : AspisR1ClaimsUnrolledParent.Record)
 (off : Usize) (out : Array ParentQM n) (h : sourceDecode n r off = .ok (.Ok out)) :
 LIB_VArray.Canonical (toMainArray out) := by
 unfold sourceDecode at h
 cases hr : AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord r) off with
 | fail e => simp only [hr] at h;cases h
 | div => simp only [hr] at h;cases h
 | ok reply =>
  cases reply with
  | Err e => simp only [hr] at h;cases h
  | Ok a =>
   simp only [hr] at h
   have same := core.result.Result.Ok.inj (Result.ok.inj h)
   subst out
   rw [array_back]
   exact decodeMain_success_members_canonical n (toMainRecord r) off a hr
theorem rows_canonical (r : AspisR1ClaimsUnrolledParent.Record)
 (value : AspisR1ClaimsUnrolledParent.Claims)
 (h : AspisR1ClaimsUnrolledParent.decodeRows NJT_ClaimsRef_Value.external r = .ok (.Ok value)) : AllRows value := by
 unfold AspisR1ClaimsUnrolledParent.decodeRows at h
 dsimp only [NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external] at h
 cases ha : sourceDecode 29#usize r 0#usize with
 | fail e => simp only [ha,bind_tc_fail] at h;cases h
 | div => simp only [ha,bind_tc_div] at h;cases h
 | ok ra =>
  cases ra with
  | Err e => simp only [ha,bind_tc_ok] at h;cases h
  | Ok a =>
   simp only [ha,bind_tc_ok] at h
   cases hb : sourceDecode 29#usize r 29#usize with
   | fail e => simp only [hb,bind_tc_fail] at h;cases h
   | div => simp only [hb,bind_tc_div] at h;cases h
   | ok rb =>
    cases rb with
    | Err e => simp only [hb,bind_tc_ok] at h;cases h
    | Ok b =>
     simp only [hb,bind_tc_ok] at h
     cases hc : sourceDecode 29#usize r 58#usize with
     | fail e => simp only [hc,bind_tc_fail] at h;cases h
     | div => simp only [hc,bind_tc_div] at h;cases h
     | ok rc =>
      cases rc with
      | Err e => simp only [hc,bind_tc_ok] at h;cases h
      | Ok c =>
       simp only [hc,bind_tc_ok] at h
       have same := core.result.Result.Ok.inj (Result.ok.inj h)
       subst value
       intro row mem
       simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
       rcases mem with rfl|rfl|rfl
       · exact source_canonical _ _ _ _ ha
       · exact source_canonical _ _ _ _ hb
       · exact source_canonical _ _ _ _ hc
theorem decode_canonical (pre : AspisR1ClaimsUnrolledParent.r1_wire.Prefix)
 (value : AspisR1ClaimsUnrolledParent.Claims)
 (h : NJT_ClaimsRef_Value.decode pre = .ok (.Ok value)) : AllRows value := by
 unfold NJT_ClaimsRef_Value.decode at h
 cases hr : sourceRecord pre 25#u8 with
 | fail e => simp only [hr,bind_tc_fail] at h;cases h
 | div => simp only [hr,bind_tc_div] at h;cases h
 | ok reply =>
  cases reply with
  | Err e => simp only [hr,bind_tc_ok] at h;cases h
  | Ok r => simp only [hr,bind_tc_ok] at h;exact rows_canonical r value h
theorem pure_canonical (p : Prefix) :
 ∃ value,NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
 (fromMainPrefix (prefixRaw p)))=.ok (.Ok value) ∧ AllRows value := by
 obtain ⟨value,h⟩ := NJT_AllocationLift.pure_success p.source p.parsed p.parse_eq
 refine ⟨value,h,?_⟩
 exact decode_canonical _ value ((NJT_ClaimsRef_Value.reference _).symm.trans h)
#print axioms array_back
#print axioms source_canonical
#print axioms rows_canonical
#print axioms decode_canonical
#print axioms pure_canonical
end LIB_VClaimsCanonical
