import R1Z.PV_RunJoin_WideImage43
import R1Z.PV_RunJoin_EncodedComplete41
import R1Z.ProverCommitOpeningBytes49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedImage43
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 PV_RunJoin_WideImage43
variable [ExternalTypes]

def values (count : Usize) (p : Nat → Raw) : Slice W :=
  Array.to_slice (ProverCommitArray49.array count (fun i => PV_RunJoin_WideImage43.source (p i)))

theorem entry (count : Usize) (p : Nat → Raw) (i : Nat) (hi : i<count.val) :
    PV_RunJoin_EncodedStep41.entry (values count p) i=PV_RunJoin_WideImage43.source (p i) := by
  change (List.ofFn (fun j : Fin count.val => PV_RunJoin_WideImage43.source (p j.val)))[i]?.getD _=PV_RunJoin_WideImage43.source (p i)
  simp only [List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some]

def image (n start : Nat) (p : Nat → Raw) (hc : ∀ (i : Nat), start ≤ i → i < start + n → canonical (p i)) : List UInt8 :=
  (List.ofFn (fun i : Fin n => List.ofFn
    (ProverCommitWideBytes48.sourceCell (p (start+i.val))
      (hc _ (by omega) (by have := i.isLt;omega))))).flatten

theorem payload (count : Usize) (p : Nat → Raw) (n start : Nat)
    (bound : start+n≤count.val) (hc : ∀ i, i<count.val → canonical (p i)) :
    (PV_RunJoin_EncodedLoop41.payload (values count p) start n).map byte=
      image n start p (fun i lo hi => hc i (by omega)) := by
  induction n generalizing start with
  | zero => simp only [PV_RunJoin_EncodedLoop41.payload,image,List.ofFn_zero,List.flatten_nil,List.map_nil]
  | succ n ih =>
    rw [PV_RunJoin_EncodedLoop41.payload,List.map_append,entry count p start (by omega),
      PV_RunJoin_WideImage43.image (p start) (hc start (by omega)),ih (start+1) (by omega)]
    simp only [image,List.ofFn_succ,List.flatten_cons]
    congr 1
    · rfl
    · congr 1
      funext i
      congr 2 <;> omega

theorem encode (ops : ExternalFuns) (count : Usize) (p : Nat → Raw)
    (hc : ∀ i, i<count.val → canonical (p i)) (room : 32*count.val≤Usize.max) :
    ∃ next, @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops)
      (values count p)=.ok next ∧
      next.val.map byte=ProverCommitOpeningBytes49.stream count.val p hc := by
  have len : (values count p).length=count.val := by
    rw [values,Array.length_to_slice]
  obtain ⟨next,hn,hv,hl⟩ := PV_RunJoin_EncodedComplete41.encode ops (values count p) (by rw [len];exact room)
  refine ⟨next,hn,?_⟩
  rw [hv,len,payload count p count.val 0 (by omega) hc]
  simp only [image,ProverCommitOpeningBytes49.stream,Nat.zero_add]
#print axioms entry
#print axioms payload
#print axioms encode
end R1Z.PV_RunJoin_EncodedImage43
