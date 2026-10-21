import OraclePortRowAwareGateWitnessD5

/-! A five-query clean prefix including the recognised frozen node.
No oracle answer equals iv, a preceding answer, or a parsed target available
at that query. The bound Q is arbitrary, so Small cannot hide a collision. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareNoCollisionD6
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionMultiDecoder OraclePortRowAwareWitnessD2
open OraclePortRowAwareGateWitnessD5

def Safe : List (Bytes × State) → List (Bytes × State) → Prop
  | _, [] => True
  | prior, q::rest => q.2 ≠ SelectedTranscriptParams.params.iv ∧
      (∀ r ∈ prior, r.2 ≠ q.2) ∧
      (∀ b ∈ q.1 :: prior.map Prod.fst, ∀ j : Fin 5,
        BinRawByteCollisionTargets.pred j b ≠ some q.2) ∧
      Safe (q::prior) rest

theorem safe_no_collision (prior tr : List (Bytes × State))
    (T : Table Bytes State) (Q : Nat)
    (hcover : ∀ a v, T a = some v → (a,v) ∈ prior)
    (hs : Safe prior tr) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) T tr := by
  induction tr generalizing prior T with
  | nil => exact id
  | cons q rest ih =>
    obtain ⟨hiv,hprev,htarget,hrest⟩ := hs
    intro hbad
    rcases hbad with ⟨_,_,h|⟨b,h⟩|⟨j,b,hb,h⟩⟩ | htail
    · exact hiv h
    · exact hprev (b,q.2) (hcover b q.2 h) rfl
    · have hm : b ∈ q.1 :: prior.map Prod.fst := by
        rcases hb with rfl | hb
        · exact List.mem_cons_self
        · cases hT : T b with
          | none => exact False.elim (hb hT)
          | some v => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(b,v),hcover b v hT,rfl⟩)
      exact htarget b hm j h
    · apply ih (q::prior) (put T q.1 q.2) _ hrest htail
      intro a v hav
      by_cases he : a = q.1
      · subst a
        have hv : q.2 = v := by simpa [put] using hav
        subst v
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hcover a v (by simpa [put,he] using hav))

def cleanTrace : List (Bytes × State) := past ++ [(node,fun _ => 6)]

/-- Normalize just the small byte lists; never reduce the padded addresses. -/
theorem clean_safe : Safe [] cleanTrace := by
  unfold cleanTrace past
  simp only [initial,PublicInitFrame.addr_bytes,row0,PublicInitFrame.row0,
    advanced,squeezed,absorbA,advanceA,squeezeA,Addr.toBytes_ofBytes]
  simp only [List.cons_append,List.nil_append,Safe,List.map_cons,List.map_nil,
    List.forall_mem_cons,List.forall_mem_nil,true_and,and_true]
  decide

theorem clean_no_collision (Q : Nat) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable cleanTrace := by
  exact safe_no_collision [] cleanTrace emptyTable Q (by intro a v h; cases h) clean_safe

#print axioms safe_no_collision
#print axioms clean_safe
#print axioms clean_no_collision
end AspisR1.OraclePortRowAwareNoCollisionD6
end
