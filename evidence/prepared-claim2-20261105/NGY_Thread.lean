import NGY_Loop
import NGY_FieldOracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Thread
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

def Chain : Native → List NGY_Oracle.Entry → Native → Prop
 | first,[],last => first=last
 | first,e::tail,last => e.before=first ∧ Chain e.after tail last

def Valid (e : NGY_Oracle.Entry) : Prop :=
 canonE e.value ∧ canonQ e.scalar ∧ e.before.count.val<29 ∧
 FIo_Native.fast_pairing.EbyKDot.push e.before e.value e.scalar=ok (e.reply,e.after)

/-- An observed child poststate, not a fresh replacement state, receives the
same invariant. The push observation is supplied by the CLOSED child packet. -/
theorem logged_post (before after : Native) (value : NE) (scalar : NQ) (lane : Nat)
 (hl : lane<29) (bounded : NGU_LPm_PublicFold.Bounded before lane)
 (cv : canonE value) (cq : canonQ scalar)
 (push : FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after)) :
 NGU_LPm_PublicFold.Bounded after (lane+1) := by
 obtain ⟨derived,call,bnext,rest⟩ := NGU_LPm_PublicFold.step before value scalar lane hl bounded cv cq
 have same : derived=after := congrArg Prod.snd (Result.ok.inj (call.symm.trans push))
 rw [←same]
 exact bnext

/-- Encode the existing linked trace as complete before/after log entries.
No local step can swap in an unrelated prestate after logging a poststate. -/
theorem records {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
 {g : Array Concrete.E 29#usize} {point : Usize} {iter : ClaimScalar.Range}
 {before : Native} {xs : List (NE×NQ)} {out : NE}
 (tr : NGU_LPm_PointLoop.Trace sem y1 g point iter before xs out) :
 ∃ entries last, Chain before entries last ∧
  entries.map (fun e => (e.value,e.scalar))=xs ∧
  (∀ e ∈ entries, Valid e) ∧ FIo_Native.fast_pairing.EbyKDot.finish last=ok out := by
 induction tr with
 | done iter iter' s out next finish =>
  exact ⟨[],s,rfl,rfl,by simp,finish⟩
 | @step iter iter' s s' out xs lane v q next read weight cv cq count push tail ih =>
  obtain ⟨entries,last,chain,mapped,valid,finish⟩ := ih
  let e : NGY_Oracle.Entry := ⟨v,q,s,s',.Ok ()⟩
  refine ⟨e::entries,last,⟨rfl,chain⟩,?_,?_,finish⟩
  · change (v,q)::entries.map (fun e => (e.value,e.scalar))=(v,q)::xs
    rw [mapped]
  · intro z hz
    rcases List.mem_cons.mp hz with same|member
    · subst z
      exact ⟨cv,cq,count,push⟩
    · exact valid z member

/-- Construct the full same-state log by the already checked invariant
induction, then consume the existing point-loop source theorem. -/
theorem from_invariant {H : Type} (inst : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
 (point : Usize) (domain : NGU_LPq_PointConstruct.ReadDomain sem y1 g point)
 (iter : ClaimScalar.Range) (before : Native)
 (last : iter.end.val=29) (bound : iter.start.val≤29)
 (bounded : NGU_LPm_PublicFold.Bounded before iter.start.val) :
 ∃ entries final out, Chain before entries final ∧ (∀ e ∈ entries, Valid e) ∧
  FIo_Native.fast_pairing.EbyKDot.finish final=ok out ∧
  verifier.prepared_claim_dot_loop NGU_LPm_PointLoop.ops inst iter sem y1 g point (statePort before)=
   ok (.Ok (ePort out)) := by
 obtain ⟨xs,out,tr,model⟩ := NGY_Loop.from_invariant inst sem y1 g point domain iter before last bound bounded
 obtain ⟨entries,final,chain,mapped,valid,finish⟩ := records tr
 exact ⟨entries,final,out,chain,valid,finish,model⟩

#print axioms logged_post
#print axioms records
#print axioms from_invariant
end AspisR1.NGY_Thread
end
