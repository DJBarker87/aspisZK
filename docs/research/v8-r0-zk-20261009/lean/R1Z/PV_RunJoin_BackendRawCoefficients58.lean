import R1Z.PV_RunJoin_BackendFullProducer58
import R1Z.PV_RunJoin_CoefficientsWeight46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendRawCoefficients58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_BackendMatrix58
open PV_RunJoin_BackendMRows58 ProverCommitPrimitive47 ProverCommitNativeOps47
abbrev Q := aspis_core.field.QM31

def coefficients (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d : Array Q 1024#usize) (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize)
    (l j : Nat) : Old.Q :=
  if l<26 then normalize (PV_RunJoin_BackendMInput58.raw (element columns hlen l j))
  else if l=26 then normalize (PV_RunJoin_SemanticScalar50.raw
    (PV_RunJoin_BackendQInput58.element (PV_RunJoin_BackendHRows58.array h hh) j))
  else if l=27 then normalize (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_BackendQInput58.element g j))
  else normalize (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_BackendQInput58.element d j))

theorem canonical (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d : Array Q 1024#usize) (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize)
    (l j : Nat) : ProverCommitSubfieldOps47.Canonical (coefficients columns hlen d h hh g l j) := by
  unfold coefficients
  split <;> first | exact normalize_canonical _ | skip
  split <;> first | exact normalize_canonical _ | skip
  split <;> exact normalize_canonical _

theorem matrix (p : Nat → Nat → W) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d : Array Q 1024#usize) (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize) :
    PV_RunJoin_BackendMatrix58.matrix (PV_RunJoin_BackendFullProducer58.final p columns hlen d h hh g)=
      PV_RunJoin_BackendMatrix58.matrix (fun l j => ProverRwDictionaryTower.fromW
        (embedded (coefficients columns hlen d h hh g l j))) := by
  apply PV_RunJoin_BackendRepresentation58.matrix_congr
  intro l hl j hj
  unfold PV_RunJoin_BackendFullProducer58.final PV_RunJoin_BackendC2Producer58.final PV_RunJoin_BackendC1Producer58.final
  rw [PV_RunJoin_BackendPrefix58.full _ _ _ l j hj]
  rw [PV_RunJoin_BackendPrefix58.full _ _ _ l j hj]
  rw [PV_RunJoin_BackendPrefix58.full _ _ _ l j hj]
  unfold PV_RunJoin_BackendBasePrefix58.bases coefficients
  by_cases hb : l<26
  · have h26 : l≠26 := by omega
    have h27 : l≠27 := by omega
    simp only [if_neg h27,if_neg h26,if_pos hb,PV_RunJoin_BackendMRows58.values,PV_RunJoin_BackendMInput58.value]
  · by_cases h26 : l=26
    · subst l
      simp only [show ¬26=27 from by decide,if_false,if_true,show ¬26<26 from by omega,
        PV_RunJoin_BackendQInput58.values,PV_RunJoin_BackendQInput58.embed]
    · by_cases h27 : l=27
      · subst l
        simp only [if_true,show ¬27<26 from by omega,show ¬27=26 from by omega,if_false,
          PV_RunJoin_BackendQInput58.values,PV_RunJoin_BackendQInput58.embed]
      · have he : l=28 := by omega
        subst l
        simp only [show ¬28=27 from by decide,show ¬28=26 from by decide,show ¬28<26 from by decide,
          if_false,if_true,PV_RunJoin_BackendQInput58.values,PV_RunJoin_BackendQInput58.embed]

#print axioms canonical
#print axioms matrix
end R1Z.PV_RunJoin_BackendRawCoefficients58
