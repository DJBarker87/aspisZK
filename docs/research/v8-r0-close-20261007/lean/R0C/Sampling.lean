import R0FS.Protocol
import AspisV8R19.SamplerWords
import AspisV8R19.SamplerFieldDecode
import AspisV8R19.R412LegalQueryEnumeration

/-! Proposed one-block total rule, recorded in FS_LOG BEFORE proof work.
It retains R601's canonical limb decoder and R417's LegalQuery meaning.
Rejected or exhausted draws DEFAULT; they are never conditioned away.
This definition is NOT the tree's multi-block retry sampler, and its law is
refuted by SamplerObstruction.noSamplerLawsD already at round zero. -/
set_option autoImplicit false
namespace R0C.Sampling
open AspisV8R19.SourceDuplexStep AspisV8R19.SamplerWords
open AspisV8R19.SamplerFieldDecode AspisV8R19.Q22WordScan
open AspisV8R19.R412LegalQueryEnumeration AspisWideTower AspisCircleGroupOrder
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Eight canonical low-31-bit limbs in source little-endian word order. -/
def limb (s : State) (j : Fin 8) : Nat := masked 31 (word s j)

def canonical (s : State) : Prop := ∀ j, limb s j < P

def decode (s : State) : WideExact :=
  ⟨decode4 (limb s 0) (limb s 1) (limb s 2) (limb s 3),
   decode4 (limb s 4) (limb s 5) (limb s 6) (limb s 7)⟩

def gamma (s : State) : WideExact :=
  if canonical s ∧ decode s ≠ 0 then decode s else 1

def ordinary (s : State) : WideExact := if canonical s then decode s else 0

/-- LegalQuery is an ordered injection; sigma uses its unordered image. -/
def defaultLegalQuery : LegalQuery :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩,
   fun _ _ h => Fin.ext (congrArg (fun j : Fin (2^18) => j.val) h)⟩

def defaultSet : Finset (Fin 262144) := Finset.univ.image defaultLegalQuery.val

/-- Stop after the available block, retaining the source scan's order and
mask. A successful set would be returned; exhaustion defaults to 0,...,21. -/
def queries (s : State) : Finset (Fin 262144) :=
  let xs := (scan ⟨[],0⟩ (words 18 s)).1.accepted
  let S := xs.toFinset.image (fun n => (⟨n % 262144, Nat.mod_lt _ (by decide)⟩ : Fin 262144))
  if S.card = 22 then S else defaultSet

/-- Total sampling rule requested in A1. Its ideal mass bounds are false. -/
def σ : Nat → State → R0FS.Chal WideExact
  | 0, s => .field (gamma s)
  | 1, s => .field (ordinary s)
  | 2, s => .field (ordinary s)
  | 3, s => .field (ordinary s)
  | 4, s => .set (queries s)
  | _, _ => .field 0

theorem gamma_ne_zero (s : State) : gamma s ≠ 0 := by
  unfold gamma
  split_ifs with h
  · exact h.2
  · exact one_ne_zero

theorem defaultSet_card : defaultSet.card = 22 := by
  rw [defaultSet, Finset.card_image_of_injective _ defaultLegalQuery.property]
  exact Finset.card_fin 22

theorem queries_card (s : State) : (queries s).card = 22 := by
  unfold queries
  dsimp only
  split_ifs with h
  · exact h
  · exact defaultSet_card

#print axioms gamma_ne_zero
#print axioms defaultSet_card
#print axioms queries_card
end
end R0C.Sampling
