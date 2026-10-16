import BackgroundAddressFollow
import BackgroundAddressRestriction
import RawBoundedTrace

/-! Reuse a proved canonical legacy background sampler on unrestricted raw
byte traces. Both successful follow and the independent-answer law are exact.
The padded-address toBytes map is used only through its canonical subtype. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawBackgroundCompletion
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.OracleResampling
open BackgroundAddressMap CanonicalByteAddress CanonicalAddressEmbedding
variable {L : Nat} {X C : Type}

def own (s : BS (Addr L) State X) (hs : AllLabels Canonical s) : BS Bytes State X :=
  rename (CanonicalRawTrace.embedding L).embed (restrict Canonical s hs)

def pending (ps : List (Addr L × Option State)) (hp : ∀ q ∈ ps, Canonical q.1) :
    List (Bytes × Option State) :=
  pendMap (CanonicalRawTrace.embedding L).embed
    (BackgroundAddressRestriction.pend Canonical ps hp)

theorem blaw_eq (g : X → List State → C) (obs : C → ℚ)
    (s : BS (Addr L) State X) (ps : List (Addr L × Option State))
    (hs : AllLabels Canonical s) (hp : ∀ q ∈ ps, Canonical q.1) :
    blaw g obs (own s hs) (pending ps hp) = blaw g obs s ps := by
  classical
  unfold own pending
  rw [blaw_rename, BackgroundAddressRestriction.blaw_restrict]

theorem bfollow_eq (g : X → List State → C) (tr : List (Bytes × State))
    (T : Table Bytes State) (s : BS (Addr L) State X)
    (ps : List (Addr L × Option State))
    (hs : AllLabels Canonical s) (hp : ∀ q ∈ ps, Canonical q.1) :
    bfollow g tr (own s hs) (pending ps hp) T =
      bfollow g (RawBoundedTrace.trace L tr) s ps (RawBoundedTrace.table L T) := by
  classical
  let rs := restrict Canonical s hs
  let rp := BackgroundAddressRestriction.pend Canonical ps hp
  have hr := BackgroundAddressFollow.bfollow_project
    (CanonicalRawTrace.embedding L) g tr rs rp T
  have hb := BackgroundAddressFollow.bfollow_project
    (RawBoundedTrace.boundedEmbedding L) g (RawBoundedTrace.trace L tr) rs rp
      (RawBoundedTrace.table L T)
  have hS : rename (RawBoundedTrace.boundedEmbedding L).embed rs = s :=
    rename_restrict Canonical s hs
  have hP : pendMap (RawBoundedTrace.boundedEmbedding L).embed rp = ps :=
    BackgroundAddressRestriction.pendMap_pend Canonical ps hp
  have htr : (RawBoundedTrace.boundedEmbedding L).project (RawBoundedTrace.trace L tr) =
      (CanonicalRawTrace.embedding L).project tr :=
    (RawBoundedTrace.boundedEmbedding L).project_imageTrace _
  have hT : (RawBoundedTrace.boundedEmbedding L).pull (RawBoundedTrace.table L T) =
      (CanonicalRawTrace.embedding L).pull T :=
    (RawBoundedTrace.boundedEmbedding L).pull_push _
  rw [hS,hP,htr,hT] at hb
  exact hr.trans hb.symm

#print axioms blaw_eq
#print axioms bfollow_eq
end AspisR1.RawBackgroundCompletion
end
