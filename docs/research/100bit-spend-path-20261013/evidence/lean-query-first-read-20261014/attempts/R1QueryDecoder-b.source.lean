import R1QueryFirstRead

/-! Query-round recovery wrapper.  This packages the endpoint seek and the
completion of missing squeeze values; it is not a full Fiat--Shamir decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def recover (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (endpoint : State) :=
  (DuplexSeek.seek p T 9 endpoint).map
    (fun r => (r.1, QueryCompletion.complete p T acc r.2))

theorem recover_correct (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < 8, Read tr (advanceA p (s j)))
    (a c : Addr L) (haread : Read tr a) (hcread : Read tr c)
    (hparse : (parseAbsorb a).isSome) (hroot : s 0 = H a)
    (hprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H s).2)
    (acc : Addr L → State)
    (hmissing : ∀ b, tableBefore emptyTable tr c b = none → acc b = H b) :
    recover p (tableBefore emptyTable tr c) acc (QueryFirstRead.result p H s).2 =
      some (a, (QueryFirstRead.result p H s).2) := by
  obtain ⟨k, hk, hselected, hseek, hcomplete⟩ :=
    QueryFirstRead.recover_query_before_endpoint p H tr Qtot hcons hQ hcoll
      s hstep hread a c haread hcread hparse hroot hprefix
  unfold recover
  rw [hseek]
  simp only [Option.map_some]
  rw [hcomplete acc (by
    intro j hj
    intro hnone
    exact hmissing (squeezeA p (s j)) hnone)]
  rfl

#print axioms recover_correct

end AspisR1.QueryDecoder
end
