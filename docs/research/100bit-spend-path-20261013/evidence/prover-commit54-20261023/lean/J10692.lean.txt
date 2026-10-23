import R1Z.ProverCommitEncoderGenericCollect54
/-! Finite induction for the pointer/counter schemas checked by Kani against
actual StepBy<Iter>/StepBy<Skip<Iter>> initialization, next and exhaustion.
Pointer values are represented as offsets; no library axiom is introduced. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderIterator54

structure State where
  ptr : Nat
  first : Bool
  skip : Nat
  deriving DecidableEq

def schema (parity k : Nat) : State :=
  if k=0 then ⟨0,true,parity⟩ else ⟨2*k-1+parity,false,0⟩

def step {A : Type} (data : Nat → A) (n : Nat) (s : State) : Option (A × State) :=
  let i := s.ptr + if s.first then s.skip else s.skip+1
  if i<n then some (data i,⟨i+1,false,0⟩) else none

theorem successful_step {A : Type} (data : Nat → A) (n parity k : Nat)
    (hp : parity≤1) (hk : 2*k+parity<n) :
    step data n (schema parity k)=some (data (2*k+parity),schema parity (k+1)) := by
  cases k with
  | zero =>
    have hk' : parity<n := by omega
    simp [schema,step,hk',Nat.add_comm parity 1]
  | succ k =>
    have hne : k+1≠0 := by omega
    have hne' : k+1+1≠0 := by omega
    have hptr : 2*(k+1)-1+parity+(0+1)=2*(k+1)+parity := by omega
    simp only [schema,if_neg hne,if_neg hne',step,Bool.false_eq_true,ite_false]
    change (if 2*(k+1)-1+parity+(0+1)<n then
      some (data (2*(k+1)-1+parity+(0+1)),State.mk (2*(k+1)-1+parity+(0+1)+1) false 0)
      else none)=some (data (2*(k+1)+parity),State.mk (2*(k+1+1)-1+parity) false 0)
    rw [hptr,if_pos hk]
    have hs : State.mk (2*(k+1)+parity+1) false 0=State.mk (2*(k+1+1)-1+parity) false 0 :=
      congrArg (fun ptr => State.mk ptr false 0) (by omega)
    exact congrArg (fun state => some (data (2*(k+1)+parity),state)) hs

theorem exhausted {A : Type} (data : Nat → A) (count parity : Nat) (hp : parity≤1) :
    step data (2*count) (schema parity count)=none := by
  by_cases hz : count=0
  · subst count;simp [schema,step]
  · have hptr : 2*count-1+parity+(0+1)=2*count+parity := by omega
    simp [schema,hz,step,hptr,show ¬2*count+parity<2*count by omega]

def collect {A : Type} (data : Nat → A) (n : Nat) : Nat → State → Option (List A)
 | 0,_ => some []
 | left+1,s => do
   let (x,next) ← step data n s
   let tail ← collect data n left next
   some (x::tail)

theorem exact_sequence {A : Type} (data : Nat → A) (count parity k left : Nat)
    (hp : parity≤1) (bound : k+left≤count) :
    collect data (2*count) left (schema parity k)=
      some (List.ofFn (fun i : Fin left => data (2*(k+i.val)+parity))) := by
  induction left generalizing k with
  | zero => simp [collect]
  | succ left ih =>
    rw [collect,successful_step data (2*count) parity k hp (by omega)]
    change (collect data (2*count) left (schema parity (k+1))).bind
      (fun tail => some (data (2*k+parity)::tail))=_
    rw [ih (k+1) (by omega)]
    change some (data (2*k+parity)::List.ofFn (fun i : Fin left => data (2*(k+1+i.val)+parity)))=_
    rw [List.ofFn_succ]
    congr 3
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

theorem matches_owned {E : Type} (inst : AspisR1ProducerRelease47.scalar.CodeField E)
    (data : Nat → E) (count : Nat) (hcount : count≤128)
    (c : Aeneas.Std.Slice E) (hc : c.val=List.ofFn (fun i : Fin (2*count) => data i.val))
    (parity left : Aeneas.Std.Usize) (hp : parity.val≤1) (hl : left.val=count) :
    ∃ out : Aeneas.Std.alloc.vec.Vec E,
      AspisR1ProducerRelease47.generic54.collect inst c 2#usize parity 0#usize left
        (Aeneas.Std.alloc.vec.Vec.new E)=Aeneas.Std.Result.ok out ∧
      collect data (2*count) count (schema parity.val 0)=some out.val := by
  obtain ⟨out,hout,hlist⟩ := ProverCommitEncoderGenericCollect54.collect inst c 2#usize parity 0#usize left count hl
    (by change 0+count<1025;omega) (by decide) (by omega)
    (by intro k hk;rw [hc,List.length_ofFn];change 2*(0+k)+parity.val<2*count;omega)
    (Aeneas.Std.alloc.vec.Vec.new E) (by change 0+count≤1024;omega)
  refine ⟨out,hout,?_⟩
  have he : out.val=List.ofFn (fun i : Fin count => data (2*i.val+parity.val)) := by
    simpa only [Aeneas.Std.alloc.vec.Vec.new,List.nil_append,hc,List.getElem_ofFn,
      show (0#usize).val=0 from rfl,show (2#usize).val=2 from rfl,Nat.zero_add] using hlist
  rw [he]
  simpa only [Nat.zero_add] using exact_sequence data count parity.val 0 count hp (by omega)

#print axioms successful_step
#print axioms exhausted
#print axioms exact_sequence
#print axioms matches_owned
end R1Z.ProverCommitEncoderIterator54
