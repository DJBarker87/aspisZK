import R1JointPrefixAnswers
import R1QueryNextLaw

/-! One next-round sampler law over the joint missing-answer set for the
completed record prefix and recovered query. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointNextLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

abbrev Completed (M Cv : Type) (L : Nat) :=
  List (M × Chal Cv) × QueryNextLaw.Recovered L

def output (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (i : Nat) (x : State)
    (as : List State) : Completed M Cv L × Chal Cv :=
  let n := (JointPrefixAnswers.missing p T rs endpoint).length
  (JointPrefixAnswers.fromAnswers p T rs endpoint (as.take n),
    (p.σ i ((as.drop n).headD default), x))

theorem output_append (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (i : Nat)
    (as bs : List State) (x : State)
    (hlen : as.length = (JointPrefixAnswers.missing p T rs endpoint).length) :
    output p T rs endpoint i x (as ++ bs) =
      (JointPrefixAnswers.fromAnswers p T rs endpoint as,
        (p.σ i (bs.headD default), x)) := by
  dsimp only [output]
  rw [List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega),
    List.drop_of_length_le (by omega), List.nil_append]

theorem background_law (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (a : Addr L) (i : Nat)
    (obs : Completed M Cv L × Chal Cv → ℚ) :
    blaw (output p T rs endpoint i) obs (QueryNextLaw.own p a)
        ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) =
      pmean (fun as => mean (fun b => mean (fun x =>
        obs (JointPrefixAnswers.fromAnswers p T rs endpoint as,
          (p.σ i b, x)))))
        ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) := by
  have hsplit := blaw_split (output p T rs endpoint i) obs (QueryNextLaw.own p a)
    ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) []
  rw [List.append_nil] at hsplit
  rw [hsplit]
  apply BackgroundMean.pmean_congr_length
  intro as has
  have hlen : as.length = (JointPrefixAnswers.missing p T rs endpoint).length := by
    simpa only [List.length_map] using has
  simp only [output_append p T rs endpoint i as _ _ hlen]
  exact QueryNextLaw.own_law p a i
    (fun c => (JointPrefixAnswers.fromAnswers p T rs endpoint as, c)) obs

theorem background_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (a : Addr L) (i : Nat)
    (obs : Completed M Cv L × Chal Cv → ℚ) (B : ℚ)
    (hfixed : ∀ as, as.length = (JointPrefixAnswers.missing p T rs endpoint).length →
      mean (fun b => mean (fun x =>
        obs (JointPrefixAnswers.fromAnswers p T rs endpoint as, (p.σ i b, x)))) ≤ B) :
    blaw (output p T rs endpoint i) obs (QueryNextLaw.own p a)
      ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) ≤ B := by
  rw [background_law]
  apply pmean_le
  intro as has
  exact hfixed as (by simpa only [List.length_map] using has)

theorem background_sampler_law {X : Type} (p : Params M Cv L)
    (T : Table (Addr L) State) (rs : List (Rec M)) (endpoint : State)
    (a : Addr L) (i : Nat)
    (mkPrefix : Completed M Cv L → Prefix X M (Chal Cv)) (m : M)
    (bad : Completed M Cv L → Chal Cv → Prop) :
    blaw (output p T rs endpoint i) (fun o => indicator (bad o.1 o.2))
        (QueryNextLaw.own p a)
        ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) =
      pmean (fun as => independentMean
        (samp p i (mkPrefix (JointPrefixAnswers.fromAnswers p T rs endpoint as)) m).toProgram
        (fun w => indicator
          (bad (JointPrefixAnswers.fromAnswers p T rs endpoint as) w.2)))
        ((JointPrefixAnswers.missing p T rs endpoint).map fun c => (c, none)) := by
  rw [background_law]
  apply BackgroundMean.pmean_congr_length
  intro as _
  exact (samp_mean p i
    (mkPrefix (JointPrefixAnswers.fromAnswers p T rs endpoint as)) m
    (bad (JointPrefixAnswers.fromAnswers p T rs endpoint as))).symm

#print axioms output_append
#print axioms background_law
#print axioms background_bound
#print axioms background_sampler_law

end AspisR1.JointNextLaw
end
