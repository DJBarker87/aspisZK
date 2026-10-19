import R1QueryNextLaw

/-! Independent-answer law for the reseeded one-round sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedSamplerLaw

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling

variable {M Cv : Type} {L : Nat}

def own (p : Params M Cv L) (a : Addr L) (reseed : State → Addr L) :
    BS (Addr L) State State :=
  .ask a fun s => .spawn (squeezeA p s)
    (.ask (advanceA p s) fun x => .ask (reseed x) fun y => .done y)

theorem own_law {C : Type} (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (obs : C → ℚ) :
    blaw (fun y bs => G (p.σ i (bs.headD default), y)) obs (own p a reseed) [] =
      mean (fun b => mean (fun y => obs (G (p.σ i b, y)))) := by
  simp only [own, blaw, pmean, List.nil_append, List.headD_cons]
  rw [mean_const, mean_const, mean_comm]

theorem background_law {X : Type} (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (pend : List (Addr L × Option State))
    (pref : List State → X) (obs : X × Chal Cv → ℚ) :
    blaw (fun y as =>
      (pref (as.take pend.length),
        (p.σ i ((as.drop pend.length).headD default), y))) obs
      (own p a reseed) pend =
    pmean (fun as => mean (fun b => mean (fun y =>
      obs (pref as, (p.σ i b, y))))) pend := by
  have hsplit := blaw_split
    (fun y as =>
      (pref (as.take pend.length),
        (p.σ i ((as.drop pend.length).headD default), y))) obs
    (own p a reseed) pend []
  rw [List.append_nil] at hsplit
  rw [hsplit]
  apply AspisR1.BackgroundMean.pmean_congr_length
  intro as hlen
  have htake (b : State) : (as ++ [b]).take pend.length = as := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdrop (b : State) : (as ++ [b]).drop pend.length = [b] := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
  have hown := own_law p a reseed i (fun ch => (pref as, ch)) obs
  simp only [own, blaw, pmean, List.nil_append, List.headD_cons, htake, hdrop] at hown ⊢
  exact hown

#print axioms own_law
#print axioms background_law

end AspisR1.ReseedSamplerLaw
end
