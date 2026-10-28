"""Focused theorem sources for the one shared ownership algebra; no Rust stand-ins."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[]
def add(name,statement):
 rows.append(name)
 (L/f'PV_OWN_{name}.lean').write_text('import R1Z.PV_OWN_Operations\nset_option autoImplicit false\nnamespace R1Z.PV_OWN_Laws\nopen PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading\nvariable {S X E T : Type}\ntheorem '+name+' '+statement+'\n#print axioms '+name+'\nend R1Z.PV_OWN_Laws\n')
add('InitLive', '''(k : Codec T) (t : Token) (c : Cell) (s : Nat) (v : T) (m : Memory)
 (h:Live m t c) : Live (writeTyped k t c s v m) t (store c s k.width (k.encode v)) := by
 exact ⟨put_same _ _ _,h.2.1,h.2.2⟩''')
add('InitOwned', '''(k : Codec T) (t : Token) (c : Cell) (slot s : Nat) (v : T) (m : Memory)
 (h:Owned m slot t c) : Owned (writeTyped k t c s v m) slot (store c s k.width (k.encode v)) := by
 exact ⟨⟨put_same _ _ _,h.1.2.1,h.1.2.2⟩,h.2.1,h.2.2⟩''')
add('InitReadable', '''(k : Codec T) (t : Token) (c : Cell) (slot s : Nat) (v : T) (m : Memory)
 (h:Readable m slot t c) : Readable (writeTyped k t c s v m) slot (store c s k.width (k.encode v)) := by
 exact ⟨⟨⟨put_same _ _ _,h.1.1.2.1,h.1.1.2.2⟩,h.1.2.1,h.1.2.2⟩,h.2⟩''')
add('InitWritable', '''(k : Codec T) (t : Token) (c : Cell) (slot s : Nat) (v : T) (m : Memory)
 (h:Writable m slot t c) : Writable (writeTyped k t c s v m) slot (store c s k.width (k.encode v)) := by
 exact ⟨⟨⟨put_same _ _ _,h.1.1.2.1,h.1.1.2.2⟩,h.1.2.1,h.1.2.2⟩,h.2⟩''')
add('InitView', '''(k : Codec T) (t : Token) (c : Cell) (s : Nat) (v : T) (m : Memory)
 (h:Live m t c) (fits:Fits c s k.width) : View k (writeTyped k t c s v m) t s v := by
 exact ⟨store c s k.width (k.encode v),⟨put_same _ _ _,h.2.1,h.2.2⟩,initialized k c s v fits⟩''')
add('InitFrame', '''(k : Codec T) (t : Token) (c : Cell) (s a : Nat) (v : T) (m : Memory)
 (h:a≠t.address) : (writeTyped k t c s v m).heap a=m.heap a := put_other _ _ _ _ h''')
add('InitOutside', '''(k : Codec T) (t : Token) (c : Cell) (s i : Nat) (v : T) (m : Memory)
 (h:i<s ∨ s+k.width≤i) :
 (store c s k.width (k.encode v)).contents i=c.contents i := outside _ _ _ _ _ h''')
add('InitIdentity', '''(k : Codec T) (t : Token) (c : Cell) (s : Nat) (v : T) (m : Memory) :
 (writeTyped k t c s v m).generations=m.generations ∧
 (writeTyped k t c s v m).slots=m.slots ∧ (writeTyped k t c s v m).loans=m.loans := ⟨rfl,rfl,rfl⟩''')
add('ReadUnique', '''(k : Codec T) (m : Memory) (t : Token) (s : Nat) (a b : T)
 (ha:View k m t s a) (hb:View k m t s b) : a=b := by
 obtain ⟨ca,la,ra⟩:=ha
 obtain ⟨cb,lb,rb⟩:=hb
 have eq : ca=cb := Option.some.inj (la.1.symm.trans lb.1)
 subst cb
 exact unique k ca s a b ra rb''')
add('TakeEmpty', '''(m : Memory) (s : Nat) : (take s m).slots s=none := by simp [take]''')
add('TakeFrame', '''(m : Memory) (s i : Nat) (h:i≠s) : (take s m).slots i=m.slots i := by simp [take,h]''')
add('TakeHeap', '''(m : Memory) (s : Nat) : (take s m).heap=m.heap ∧
 (take s m).generations=m.generations ∧ (take s m).loans=m.loans := ⟨rfl,rfl,rfl⟩''')
add('TakeIdempotent', '''(m : Memory) (s : Nat) : take s (take s m)=take s m := by
 cases m; simp only [take]; congr; funext i; by_cases h:i=s <;> simp [h]''')
add('MoveSource', '''(m : Memory) (src dst : Nat) (t : Token) (c : Cell) :
 (move src dst t c m).slots src=none := by simp [move]''')
add('MoveDestination', '''(m : Memory) (src dst : Nat) (t : Token) (c : Cell) (h:dst≠src) :
 (move src dst t c m).slots dst=some t := by simp [move,h]''')
add('MoveSlotFrame', '''(m : Memory) (src dst i : Nat) (t : Token) (c : Cell) (hs:i≠src) (hd:i≠dst) :
 (move src dst t c m).slots i=m.slots i := by simp [move,hs,hd]''')
add('MoveHeapFrame', '''(m : Memory) (src dst p : Nat) (t : Token) (c : Cell) (h:p≠t.address) :
 (move src dst t c m).heap p=m.heap p := put_other _ _ _ _ h''')
add('MoveLive', '''(m : Memory) (src dst : Nat) (t : Token) (c : Cell) (h:Live m t c) :
 Live (move src dst t c m) t {c with owner := dst} := ⟨put_same _ _ _,h.2.1,h.2.2⟩''')
add('MoveOwnership', '''(m : Memory) (src dst : Nat) (t : Token) (c : Cell)
 (h:Owned m src t c) (hd:dst≠src) :
 Owned (move src dst t c m) dst t {c with owner := dst} := by
 refine ⟨⟨put_same _ _ _,h.1.2.1,h.1.2.2⟩,?_,rfl⟩
 simp [move,hd]''')
add('MoveRepresentation', '''(k : Codec T) (c : Cell) (dst s : Nat) (v : T)
 (h:Represents k c s v) : Represents k {c with owner := dst} s v := h''')
add('BorrowHeap', '''(m : Memory) (l : Loan) : (borrow l m).heap=m.heap ∧
 (borrow l m).slots=m.slots ∧ (borrow l m).generations=m.generations := ⟨rfl,rfl,rfl⟩''')
add('BorrowRelease', '''(m : Memory) (l : Loan) : endBorrow (borrow l m)=m := rfl''')
add('BorrowOwned', '''(m : Memory) (l : Loan) (slot : Nat) (t : Token) (c : Cell)
 (h:Owned m slot t c) : Owned (borrow l m) slot t c := h''')
add('BorrowBlocksWrite', '''(m : Memory) (l : Loan) (slot : Nat) (c : Cell) :
 ¬Writable (borrow l m) slot l.token c := by
 intro h
 exact h.2 l (List.mem_cons_self) rfl''')
add('ExclusiveBlocksRead', '''(m : Memory) (l : Loan) (slot : Nat) (c : Cell) (hx:l.exclusive=true) :
 ¬Readable (borrow l m) slot l.token c := by
 intro h
 have hf:=h.2 l List.mem_cons_self rfl
 rw [hx] at hf
 cases hf''')
add('SharedRead', '''(m : Memory) (l : Loan) (slot : Nat) (t : Token) (c : Cell)
 (h:Readable m slot t c) (shared:l.exclusive=false) : Readable (borrow l m) slot t c := by
 refine ⟨h.1,?_⟩
 intro q hq ht
 cases List.mem_cons.mp hq with
 | inl eq => subst q; exact shared
 | inr hm => exact h.2 q hm ht''')
add('RetireDead', '''(m : Memory) (t : Token) (c : Cell) :
 (retire t c m).heap t.address=some {c with live := false} := put_same _ _ _''')
add('RetireNoLive', '''(m : Memory) (t : Token) (c d : Cell) : ¬Live (retire t c m) t d := by
 intro h
 have eq:{c with live := false}=d := Option.some.inj ((put_same _ _ _).symm.trans h.1)
 subst d
 cases h.2.1''')
add('RetireFrame', '''(m : Memory) (t : Token) (c : Cell) (a : Nat) (h:a≠t.address) :
 (retire t c m).heap a=m.heap a := put_other _ _ _ _ h''')
add('RetireBytes', '''(c : Cell) : ({c with live := false} : Cell).contents=c.contents ∧
 ({c with live := false} : Cell).size=c.size ∧
 ({c with live := false} : Cell).alignment=c.alignment := ⟨rfl,rfl,rfl⟩''')
# Runtime branches are complete outcomes, never just successful return values.
for label,pattern in [('Null','.ok none'),('Failure','.fail e'),('Divergence','.div')]:
 extra='(e:E)' if label=='Failure' else ''
 add('Alloc'+label,f'''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner : Nat)
 (w : State S X) (s : S) {extra} (h:prim r w.allocator=({pattern},s)) :
 (allocate prim r owner w).world={{w with allocator := s}} := by simp [allocate,emit,h]''')
add('AllocSuccess', '''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner p : Nat)
 (w : State S X) (s : S) (h:prim r w.allocator=(.ok (some p),s)) :
 (allocate prim r owner w).world.memory.heap p=some (emptyCell r.size r.alignment owner) := by
 simp [allocate,emit,h,put]''')
add('AllocGeneration', '''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner p : Nat)
 (w : State S X) (s : S) (h:prim r w.allocator=(.ok (some p),s)) :
 (allocate prim r owner w).world.memory.generations p=w.memory.generations p+1 := by
 simp [allocate,emit,h]''')
add('AllocTrace', '''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner : Nat)
 (w : State S X) : (allocate prim r owner w).calls=[(w,.allocate r.size r.alignment)] := rfl''')
add('AllocFresh', '''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (w : State S X)
 (p : Nat) (s : S) (adequate:AllocatorAdequate prim r w) (h:prim r w.allocator=(.ok (some p),s)) :
 p≠0 ∧ r.alignment>0 ∧ p%r.alignment=0 := by
 obtain ⟨a,b,c,_⟩:=adequate p s h
 exact ⟨a,b,c⟩''')
add('AllocDisjoint', '''(prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (w : State S X)
 (p q : Nat) (s : S) (c : Cell) (adequate:AllocatorAdequate prim r w)
 (h:prim r w.allocator=(.ok (some p),s)) (old:w.memory.heap q=some c) (live:c.live=true) :
 q+c.size≤p ∨ p+r.size≤q := (adequate p s h).2.2.2 q c old live''')
add('AllocSpareUninit', '''(r : Request) (owner i : Nat) : (emptyCell r.size r.alignment owner).contents i=none := rfl''')
add('FreeTrace', '''(prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).calls=[(w,.deallocate t.address c.size c.alignment)] := rfl''')
add('FreeOutcome', '''(prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).outcome=(prim t.address ⟨c.size,c.alignment⟩ w.allocator).1 := rfl''')
add('FreeAllocator', '''(prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).world.allocator=(prim t.address ⟨c.size,c.alignment⟩ w.allocator).2 := rfl''')
add('FreeExtra', '''(prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).world.extra=w.extra := rfl''')
add('DropPod', '''(w : State S X) : (dropPod (E:=E) w).outcome=.ok () ∧
 (dropPod (E:=E) w).world=w ∧ (dropPod (E:=E) w).calls=[] := ⟨rfl,rfl,rfl⟩''')
add('DropString', '''(prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) :
 dropString (X:=X) prim t c=dropVecPod prim t c := rfl''')
add('DropOwnedAbsent', '''(slot : Nat) (glue : Token → Action S X E Unit) (w : State S X)
 (h:w.memory.slots slot=none) : (dropOwned slot glue w).calls=[] := by simp [dropOwned,h]''')
add('DropOwnedPresent', '''(slot : Nat) (glue : Token → Action S X E Unit) (w : State S X) (t : Token)
 (h:w.memory.slots slot=some t) :
 dropOwned slot glue w=glue t {w with memory := take slot w.memory} := by simp [dropOwned,h]''')
add('DropConsumeBeforeGlue', '''(slot : Nat) (w : State S X) :
 (take slot w.memory).slots slot=none := by simp [take]''')
add('SequenceEmpty', '''(w : State S X) : (sequence (E:=E) [] w).calls=[] ∧
 (sequence (E:=E) [] w).world=w ∧ (sequence (E:=E) [] w).outcome=.ok () := ⟨rfl,rfl,rfl⟩''')
add('SequenceFailure', '''(a : Action S X E Unit) (rest : List (Action S X E Unit)) (w : State S X)
 (e : E) (h:(a w).outcome=.fail e) :
 sequence (a::rest) w=⟨.fail e,(a w).world,(a w).calls⟩ := bind_fail a _ w e h''')
add('SequenceDivergence', '''(a : Action S X E Unit) (rest : List (Action S X E Unit)) (w : State S X)
 (h:(a w).outcome=.div) :
 sequence (a::rest) w=⟨.div,(a w).world,(a w).calls⟩ := bind_div a _ w h''')
add('TruncateCapacity', '''(v : Vector T) (n : Nat) : (truncate n v).capacity=v.capacity ∧
 (truncate n v).token=v.token ∧ (truncate n v).owner=v.owner := ⟨rfl,rfl,rfl⟩''')
add('TruncateLength', '''(v : Vector T) (n : Nat) : (truncate n v).values.length=min n v.values.length := by
 exact List.length_take''')
add('VecBound', '''(k : Codec T) (m : Memory) (v : Vector T) (h:VecView k m v) :
 v.values.length≤v.capacity := h.choose_spec.2.2.2.1''')
add('VecCell', '''(k : Codec T) (m : Memory) (v : Vector T) (h:VecView k m v) :
 ∃ c, Owned m v.owner v.token c ∧ c.size=v.capacity*k.width := by
 obtain ⟨c,a,b,_⟩:=h
 exact ⟨c,a,b⟩''')
add('BoxInitialized', '''(k : Codec T) (m : Memory) (o : Nat) (t : Token) (v : T) (h:BoxView k m o t v) :
 View k m t 0 v := by
 obtain ⟨c,a,_,_,b⟩:=h
 exact ⟨c,a.1,b⟩''')
add('StringUtf8', '''(k : Codec UInt8) (utf8 : List UInt8 → Prop) (m : Memory) (v : Vector UInt8)
 (h:StringView k utf8 m v) : utf8 v.values := h.2''')
add('ArrayRead', '''(k : Codec T) (c : Cell) (start i : Nat) (xs : List T) (x : T)
 (h:ArrayView k c start xs) (hi:xs[i]?=some x) : Represents k c (start+i*k.width) x := h.2 i x hi''')
(L.parent.parent.parent.parent.parent if False else R/'evidence/pv-own-20261028/law-targets.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows))
