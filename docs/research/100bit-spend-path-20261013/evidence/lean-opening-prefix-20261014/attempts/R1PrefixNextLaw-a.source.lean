import R1PrefixAnswers
import R1QueryNextLaw

/-! Independent-answer completion law for a recovered ordinary prefix and
its next duplex round. Freshness and trace injection are separate obligations;
the equality here does not assert independence for an arbitrary oracle trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixNextLaw
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def output (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (x : State) (as : List State) :
    List (M × Chal Cv) × Chal Cv :=
  let n := (PrefixAnswers.missing p T rs).length
  (PrefixAnswers.fromAnswers p T 0 rs (as.take n),
    (p.σ rs.length ((as.drop n).headD default), x))

theorem output_append (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (as bs : List State) (x : State)
    (hlen : as.length = (PrefixAnswers.missing p T rs).length) :
    output p T rs x (as ++ bs) =
      (PrefixAnswers.fromAnswers p T 0 rs as, (p.σ rs.length (bs.headD default), x)) := by
  have ht : (as ++ bs).take (PrefixAnswers.missing p T rs).length = as := by
    rw [← hlen, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hd : (as ++ bs).drop (PrefixAnswers.missing p T rs).length = bs := by
    rw [← hlen, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  simp only [output, ht, hd]

theorem background_law (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (a : Addr L)
    (obs : List (M × Chal Cv) × Chal Cv → ℚ) :
    blaw (output p T rs) obs (QueryNextLaw.own p a)
        ((PrefixAnswers.missing p T rs).map fun c => (c, none)) =
      pmean (fun as => mean (fun b => mean (fun x =>
        obs (PrefixAnswers.fromAnswers p T 0 rs as, (p.σ rs.length b, x)))))
        ((PrefixAnswers.missing p T rs).map fun c => (c, none)) := by
  have hsplit := blaw_split (output p T rs) obs (QueryNextLaw.own p a)
    ((PrefixAnswers.missing p T rs).map fun c => (c, none)) []
  rw [List.append_nil] at hsplit
  rw [hsplit]
  apply BackgroundMean.pmean_congr_length
  intro as has
  have hlen : as.length = (PrefixAnswers.missing p T rs).length := by
    simpa only [List.length_map] using has
  simp only [output_append p T rs as _ _ hlen]
  exact QueryNextLaw.own_law p a rs.length
    (fun ch => (PrefixAnswers.fromAnswers p T 0 rs as, ch)) obs

theorem background_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (a : Addr L)
    (obs : List (M × Chal Cv) × Chal Cv → ℚ) (B : ℚ)
    (hfixed : ∀ as, as.length = (PrefixAnswers.missing p T rs).length →
      mean (fun b => mean (fun x =>
        obs (PrefixAnswers.fromAnswers p T 0 rs as, (p.σ rs.length b, x)))) ≤ B) :
    blaw (output p T rs) obs (QueryNextLaw.own p a)
      ((PrefixAnswers.missing p T rs).map fun c => (c, none)) ≤ B := by
  rw [background_law]
  apply pmean_le
  intro as has
  exact hfixed as (by simpa only [List.length_map] using has)

theorem background_sampler_law {X : Type} (p : Params M Cv L)
    (T : Table (Addr L) State) (rs : List (Rec M)) (a : Addr L)
    (x : X) (m : M) (bad : List (M × Chal Cv) → Chal Cv → Prop) :
    blaw (output p T rs) (fun o => indicator (bad o.1 o.2)) (QueryNextLaw.own p a)
        ((PrefixAnswers.missing p T rs).map fun c => (c, none)) =
      pmean (fun as => independentMean
        (samp p rs.length (⟨x, PrefixAnswers.fromAnswers p T 0 rs as⟩ : Prefix X M (Chal Cv)) m).toProgram
        (fun w => indicator (bad (PrefixAnswers.fromAnswers p T 0 rs as) w.2)))
        ((PrefixAnswers.missing p T rs).map fun c => (c, none)) := by
  rw [background_law]
  apply BackgroundMean.pmean_congr_length
  intro as _
  exact (samp_mean p rs.length
    (⟨x, PrefixAnswers.fromAnswers p T 0 rs as⟩ : Prefix X M (Chal Cv)) m
    (bad (PrefixAnswers.fromAnswers p T 0 rs as))).symm

#print axioms output_append
#print axioms background_law
#print axioms background_bound
#print axioms background_sampler_law
end AspisR1.PrefixNextLaw
end
