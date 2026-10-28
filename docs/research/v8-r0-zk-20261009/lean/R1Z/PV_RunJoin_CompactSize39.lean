import R1Z.PV_RunJoin_CompactPayload39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactSize39
open Aeneas Aeneas.Std Result ProverRwFull

/-- Exact complete source result and independent output length together. -/
theorem encode (logical : Slice U8) (out : alloc.vec.Vec U8) (n : Nat)
    (length : logical.length=32*n) (room : out.length+16*n≤Usize.max)
    (zero : ∀ pos : Usize, pos.val%32=0 → pos.val+32≤logical.length →
      ∀ j : Usize, 16≤j.val → j.val<32 →
        Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8) :
    ∃ next, host_compact.compact_values logical out=.ok (.Ok (),next) ∧
      next.val=out.val ++
        (List.ofFn (fun i : Fin n => (logical.val.drop (32*i.val)).take 16)).flatten ∧
      next.length=out.length+16*n := by
  obtain ⟨next,hn,hval⟩ := PV_RunJoin_CompactComplete39.encode logical out n length room zero
  refine ⟨next,hn,?_,?_⟩
  · rw [hval,PV_RunJoin_CompactPayload39.indexed]
    simp only [Nat.zero_add]
  · change next.val.length=out.val.length+16*n
    rw [hval,List.length_append,PV_RunJoin_CompactPayload39.length logical 0 n (by omega)]

#print axioms encode
end R1Z.PV_RunJoin_CompactSize39
