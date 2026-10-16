import BackgroundAddressMap
import R1UnifiedDecoder
import R1CanonicalByteAddress

/-! Every possible own/background query of the existing decoder has a canonical
byte address when its input address is canonical. This covers all sampler
continuations, not only the successful execution path. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BackgroundCanonicalLabels
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open BackgroundAddressMap CanonicalByteAddress

variable {M Cv X Y : Type} {L : Nat}

def Good (s : BS (Addr L) State X) (pend : List (Addr L × Option State)) : Prop :=
  AllLabels Canonical s ∧ ∀ q ∈ pend, Canonical q.1

theorem allLabels_outputMap (f : X → Y) (s : BS (Addr L) State X)
    (h : AllLabels Canonical s) : AllLabels Canonical (BackgroundOwnMap.map f s) := by
  induction s with
  | done x => trivial
  | ask i k ih => exact ⟨h.1,fun a => ih a (h.2 a)⟩
  | spawn i n ih => exact ⟨h.1,ih h.2⟩

theorem plain (p : Params M Cv L) (a : Addr L) (ha : Canonical a) :
    AllLabels Canonical (QueryNextLaw.own p a) :=
  ⟨ha,fun _ => ⟨canonical_ofBytes _ _,⟨canonical_ofBytes _ _,fun _ => trivial⟩⟩⟩

private theorem absorb_canonical (p : Params M Cv L) (s : State)
    (l : Byte) (data : Bytes) (h : data.length ≤ p.D) :
    Canonical (absorbA p s l data h) := canonical_ofBytes _ _

theorem initial (p : Params M Cv L) (hD : 5 ≤ p.D) (a : Addr L)
    (ha : Canonical a) :
    AllLabels Canonical (InitialSamplerLaw.own p a (PublicInitFrame.row0 p hD)) :=
  ⟨ha,fun s => ⟨absorb_canonical p s 160 PublicInitFrame.emptyRecord hD,fun _ =>
    ⟨canonical_ofBytes _ _,⟨canonical_ofBytes _ _,fun _ => trivial⟩⟩⟩⟩

theorem reseed (p : Params M Cv L) (pub : UnifiedSampler.Public L) (a : Addr L)
    (ha : Canonical a) : AllLabels Canonical (UnifiedReseedDecoder.own p pub a) :=
  ⟨ha,fun _ => ⟨canonical_ofBytes _ _,⟨canonical_ofBytes _ _,fun _ =>
    ⟨canonical_ofBytes _ _,fun _ => trivial⟩⟩⟩⟩

theorem query_chain (p : Params M Cv L) (n : Nat) (s : State) (xs : List State) :
    AllLabels Canonical (QueryBackgroundChain.chainBS p n s xs) := by
  induction n generalizing s xs with
  | zero => trivial
  | succ n ih => exact ⟨canonical_ofBytes _ _,⟨canonical_ofBytes _ _,fun x => ih x (xs++[x])⟩⟩

theorem query (p : Params M Cv L) (a : Addr L) (ha : Canonical a) :
    AllLabels Canonical (UnifiedQueryDecoder.own p a) :=
  ⟨ha,fun s => query_chain p 8 s [s]⟩

theorem prefix_missing (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (a : Addr L) (ha : a ∈ PrefixAnswers.missing p T rs) :
    Canonical a := by
  obtain ⟨r,_,he⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_dedup.mp ha)).1
  rw [← he]
  exact canonical_ofBytes _ _

theorem query_missing (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (a : Addr L) (ha : a ∈ QueryDecoder.missing p T endpoint) :
    Canonical a := by
  unfold QueryDecoder.missing at ha
  cases hs : DuplexSeek.seek p T 9 endpoint with
  | none => simp [hs] at ha
  | some r =>
      rw [hs] at ha
      obtain ⟨s,_,he⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_dedup.mp ha)).1
      rw [← he]
      exact canonical_ofBytes _ _

theorem joint_missing (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (a : Addr L)
    (ha : a ∈ JointPrefixAnswers.missing p T rs endpoint) : Canonical a := by
  rcases JointPrefixAnswers.missing_cases p T rs endpoint a ha with hp | hq
  · exact prefix_missing p T rs a hp
  · exact query_missing p T endpoint a hq

theorem pend_of_canonical (as : List (Addr L)) (h : ∀ a ∈ as, Canonical a) :
    ∀ q ∈ (as.map fun a => (a,(none : Option State))), Canonical q.1 := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  exact h a ha

theorem lifted_good
    (dec : Dec (UnifiedSampler.Public L) (TranscriptView.Message M)
      (TranscriptView.Challenge Cv) (Addr L) State State)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : DecoderStateList.lift dec a T = some (own,pend,g))
    (hgood : ∀ s ps out, dec a T = some (s,ps,out) → Good s ps) : Good own pend := by
  obtain ⟨s,ps,out,hdec,he⟩ := DecoderStateList.lift_sound dec a T own pend g hd
  have hg := hgood s ps out hdec
  cases he
  exact ⟨allLabels_outputMap _ _ hg.1,hg.2⟩

#print axioms initial
#print axioms query_chain
#print axioms joint_missing
#print axioms lifted_good
end AspisR1.BackgroundCanonicalLabels
end
