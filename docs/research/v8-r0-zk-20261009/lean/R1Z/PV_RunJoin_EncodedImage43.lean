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

def image (n start : Nat) (p : Nat → Raw) : List UInt8 :=
  (List.ofFn fun i : Fin n =>
    List.ofFn (ProverCommitValueRange47.bytes (value (p (start + i.val))))).flatten

theorem payload (count : Usize) (p : Nat → Raw) (n start : Nat)
    (bound : start+n≤count.val) (hc : ∀ i, i<count.val → canonical (p i)) :
    (PV_RunJoin_EncodedLoop41.payload (values count p) start n).map byte=
      image n start p := by
  induction n generalizing start with
  | zero => simp only [PV_RunJoin_EncodedLoop41.payload,image,List.ofFn_zero,List.flatten_nil,List.map_nil]
  | succ n ih =>
    rw [PV_RunJoin_EncodedLoop41.payload,List.map_append,entry count p start (by omega),
      PV_RunJoin_WideImage43.image (p start) (hc start (by omega)),
      ProverCommitWideBytes48.source_image,ih (start+1) (by omega)]
    conv_rhs => unfold image;rw [List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    unfold image
    congr 1
    apply congrArg List.ofFn
    funext i
    have off : start+1+i.val=start+i.succ.val := by simp only [Fin.val_succ];omega
    simp only [off]

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
  have hi : image count.val 0 p=ProverCommitOpeningBytes49.modelStream count.val
      (fun i => value (p i.val)) := by
    simp only [image,ProverCommitOpeningBytes49.modelStream,Nat.zero_add]
  rw [hi]
  exact (ProverCommitOpeningBytes49.stream_image count.val p hc (fun i => value (p i.val)) (fun _ => rfl)).symm
#print axioms entry
#print axioms payload
#print axioms encode
end R1Z.PV_RunJoin_EncodedImage43
