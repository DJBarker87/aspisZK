import R1Z.ProverCommitEncoderIterator54
import R1Z.ProverCommitWideOps48
/-! Reassemble the eight independent native collector component checks into
whole words and ordered lists; then connect their output to the owned collector.
Native Kani results are external evidence, not axioms in this module. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCollection55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitWideOps48

def limb (x : Raw) : Fin 8 → U32 :=
  ![x.1.c0.a,x.1.c0.b,x.1.c1.a,x.1.c1.b,x.2.c0.a,x.2.c0.b,x.2.c1.a,x.2.c1.b]

theorem raw_ext (x y : Raw) (h : ∀ w, limb x w=limb y w) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,i⟩⟩⟩
  rcases y with ⟨⟨⟨a',b'⟩,⟨c',d'⟩⟩,⟨⟨e',f'⟩,⟨g',i'⟩⟩⟩
  have h0 : a=a' := h 0
  have h1 : b=b' := h 1
  have h2 : c=c' := h 2
  have h3 : d=d' := h 3
  have h4 : e=e' := h 4
  have h5 : f=f' := h 5
  have h6 : g=g' := h 6
  have h7 : i=i' := h 7
  cases h0;cases h1;cases h2;cases h3;cases h4;cases h5;cases h6;cases h7
  rfl

theorem list_image (out : List Raw) (n : Nat) (f : Nat → Raw)
    (hn : out.length=n)
    (h : ∀ (k : Nat) (hk : k<out.length) (w : Fin 8), limb out[k] w=limb (f k) w) :
    out=List.ofFn (fun k : Fin n => f k.val) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,hn]
  · intro k hk hj
    rw [List.getElem_ofFn]
    exact raw_ext _ _ (h k hk)

theorem matches_owner (inst : scalar.CodeField Raw) (data : Nat → Raw)
    (count : Nat) (hcount : count≤128)
    (c : Slice Raw) (hc : c.val=List.ofFn (fun k : Fin (2*count) => data k.val))
    (parity left : Usize) (hp : parity.val≤1) (hl : left.val=count)
    (native : List Raw) (hn : native.length=count)
    (hword : ∀ (k : Nat) (hk : k<native.length) (w : Fin 8),
      limb native[k] w=limb (data (2*k+parity.val)) w) :
    ∃ out : alloc.vec.Vec Raw,
      generic54.collect inst c 2#usize parity 0#usize left (alloc.vec.Vec.new Raw)=ok out ∧
      native=out.val := by
  obtain ⟨out,hout,hsequence⟩ := ProverCommitEncoderIterator54.matches_owned inst data count hcount c hc parity left hp hl
  have hm := ProverCommitEncoderIterator54.exact_sequence data count parity.val 0 count hp (by omega)
  have he : native=List.ofFn (fun k : Fin count => data (2*k.val+parity.val)) :=
    list_image native count (fun k => data (2*k+parity.val)) hn hword
  refine ⟨out,hout,?_⟩
  rw [hm] at hsequence
  have ho := Option.some.inj hsequence
  simp only [Nat.zero_add] at ho
  exact he.trans ho

#print axioms raw_ext
#print axioms list_image
#print axioms matches_owner
end R1Z.ProverCommitCollection55
