import R1Z.ProverCommitFoldSteps
import PV_L2C_ReferenceQ
import PV_L2C_QFold
set_option autoImplicit false
namespace PV_L2C_ExtractedFold
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open R1Z.ProverCommitFoldSteps PV_L2C_NativeQ PV_L2C_QBalance PV_L2C_QFold PV_L2C_ReferenceQ

def run (xs : List RawQ) (s : RawQ) : Result RawQ :=
  foldSteps (fun q sum => aspis_core.field.QM31.add sum q) xs s

theorem source (xs : List Q) (s : Q) :
    run (xs.map PV_L2C_ReferenceQ.source) (PV_L2C_ReferenceQ.source s)=
      ok (PV_L2C_ReferenceQ.source (foldQ xs s)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [run,List.map_cons,foldSteps,add_source,bind_tc_ok]
    exact ih (addQ s x)
#print axioms source

theorem canonical_sum (xs : List Q) (hc : ∀ q ∈ xs, Canonical q) :
    ∃ q : Q,
      run (xs.map PV_L2C_ReferenceQ.source) aspis_core.field.QM31.ZERO=
        ok (PV_L2C_ReferenceQ.source q) ∧ Canonical q ∧ decodeQ q=(xs.map decodeQ).sum := by
  refine ⟨foldQ xs zero,?_,canonical_fold xs hc zero zero_canonical,?_⟩
  · rw [← source_zero]
    exact source xs zero
  · rw [decode_fold xs hc zero zero_canonical,zero_decode,zero_add]
#print axioms canonical_sum

theorem zero_sum (xs : List Q) (hc : ∀ q ∈ xs, Canonical q)
    (hz : (xs.map decodeQ).sum=0) :
    run (xs.map PV_L2C_ReferenceQ.source) aspis_core.field.QM31.ZERO=
      ok aspis_core.field.QM31.ZERO := by
  obtain ⟨q,hq,hc,hd⟩ := canonical_sum xs hc
  have he : q=zero := decode_injective q zero hc zero_canonical (hd.trans (hz.trans zero_decode.symm))
  rw [hq,he,source_zero]
#print axioms zero_sum
end PV_L2C_ExtractedFold
