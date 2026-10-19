import R1QueryDecoderAnswers
import R1BackgroundMeanCongr

/-! The independent-answer law for a single duplex round after a recovered
query prefix. Missing prefix answers are averaged outside the new round.
This does not assert trace injection or a full R1 Fiat--Shamir instance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryNextLaw
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Recovered (L : Nat) := Option (Addr L × AspisV8R19.Q22SamplerProgram.Result)

def own (p : Params M Cv L) (a : Addr L) : BS (Addr L) State State :=
  .ask a fun s => .spawn (squeezeA p s) (.ask (advanceA p s) fun x => .done x)

def output (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (i : Nat) (x : State) (as : List State) :
    Recovered L × Chal Cv :=
  let n := (QueryDecoder.missing p T endpoint).length
  (QueryDecoder.fromAnswers p T endpoint (as.take n),
    (p.σ i ((as.drop n).headD default), x))

theorem own_law {C : Type} (p : Params M Cv L) (a : Addr L)
    (i : Nat) (G : Chal Cv → C) (obs : C → ℚ) :
    blaw (fun x bs => G (p.σ i (bs.headD default), x)) obs (own p a) [] =
      mean (fun b => mean (fun x => obs (G (p.σ i b, x)))) := by
  simp only [own, blaw, pmean, List.nil_append, List.headD_cons]
  rw [mean_const, mean_comm]

theorem output_append (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (i : Nat) (as bs : List State) (x : State)
    (hlen : as.length = (QueryDecoder.missing p T endpoint).length) :
    output p T endpoint i x (as ++ bs) =
      (QueryDecoder.fromAnswers p T endpoint as, (p.σ i (bs.headD default), x)) := by
  dsimp only [output]
  rw [QueryDecoder.fromAnswers_take_append p T endpoint as bs hlen,
    List.drop_append_of_le_length (by omega),
    List.drop_of_length_le (by omega), List.nil_append]

theorem background_law (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (a : Addr L) (i : Nat)
    (obs : Recovered L × Chal Cv → ℚ) :
    blaw (output p T endpoint i) obs (own p a)
        ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) =
      pmean (fun as => mean (fun b => mean (fun x =>
        obs (QueryDecoder.fromAnswers p T endpoint as, (p.σ i b, x)))))
        ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) := by
  have hsplit := blaw_split (output p T endpoint i) obs (own p a)
    ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) []
  rw [List.append_nil] at hsplit
  rw [hsplit]
  apply BackgroundMean.pmean_congr_length
  intro as has
  have hlen : as.length = (QueryDecoder.missing p T endpoint).length := by
    simpa only [List.length_map] using has
  simp only [output_append p T endpoint i as _ _ hlen]
  exact own_law p a i (fun c => (QueryDecoder.fromAnswers p T endpoint as, c)) obs

theorem background_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (a : Addr L) (i : Nat)
    (obs : Recovered L × Chal Cv → ℚ) (B : ℚ)
    (hfixed : ∀ as, as.length = (QueryDecoder.missing p T endpoint).length →
      mean (fun b => mean (fun x =>
        obs (QueryDecoder.fromAnswers p T endpoint as, (p.σ i b, x)))) ≤ B) :
    blaw (output p T endpoint i) obs (own p a)
      ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) ≤ B := by
  rw [background_law]
  apply pmean_le
  intro as has
  exact hfixed as (by simpa only [List.length_map] using has)

/-- The existing duplex sampler law can be reused for every fixed completed
prefix. `mkPrefix` is arbitrary here; its R1 meaning is an integration duty. -/
theorem background_sampler_law {X : Type} (p : Params M Cv L)
    (T : Table (Addr L) State) (endpoint : State) (a : Addr L) (i : Nat)
    (mkPrefix : Recovered L → Prefix X M (Chal Cv)) (m : M)
    (bad : Recovered L → Chal Cv → Prop) :
    blaw (output p T endpoint i) (fun o => indicator (bad o.1 o.2)) (own p a)
        ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) =
      pmean (fun as => independentMean
        (samp p i (mkPrefix (QueryDecoder.fromAnswers p T endpoint as)) m).toProgram
        (fun w => indicator (bad (QueryDecoder.fromAnswers p T endpoint as) w.2)))
        ((QueryDecoder.missing p T endpoint).map fun c => (c, none)) := by
  rw [background_law]
  apply BackgroundMean.pmean_congr_length
  intro as _
  exact (samp_mean p i (mkPrefix (QueryDecoder.fromAnswers p T endpoint as)) m
    (bad (QueryDecoder.fromAnswers p T endpoint as))).symm

#print axioms own_law
#print axioms output_append
#print axioms background_law
#print axioms background_bound
#print axioms background_sampler_law
end AspisR1.QueryNextLaw
end
