import S7Kani3GroupsLoop
import S7Kani2ConstructorInvariant
set_option autoImplicit false
namespace S7Kani3GeometryStorage
open Aeneas Aeneas.Std Result

theorem prefix_length (xs prefixes : List U32) (p : U32) :
    (S7Kani2PrefixLoop.model xs prefixes p).1.length=prefixes.length+xs.length := by
  induction xs generalizing prefixes p with
  | nil => simp [S7Kani2PrefixLoop.model]
  | cons x xs ih =>
      simpa [S7Kani2PrefixLoop.model,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using ih (prefixes++[p]) (S7Kani2PrefixLoop.wordMul p x)

/-- Storage pipeline from the actual emitted prefix loop through every
backward write to every grouped record. Geometry values and initial inverse
remain supplied here; no claim about inversion's algebraic meaning is made. -/
theorem storage_pipeline (flat prefixes inverse : alloc.vec.Vec U32)
    (groups : alloc.vec.Vec S7Kani3GroupsLoop.Group) (product suffix : U32)
    (zero count : Usize)
    (hz : zero.val=0) (hc : count.val ≤ 22)
    (hf : flat.val.length=5*count.val)
    (hp : prefixes.val=[]) (hi : inverse.val.length=flat.val.length)
    (hg : groups.val=[]) :
    ∃ ps prod inv out,
      S7Kani2PrefixLoop.prefixes_owned flat prefixes product zero=ok (flat,ps,prod) ∧
      ps.val.length=flat.val.length ∧
      S7Kani3InverseLoop.inverse_owned flat ps inverse suffix (alloc.vec.Vec.len flat)=ok inv ∧
      inv.val.length=5*count.val ∧
      S7Kani3GroupsLoop.groups_owned inv groups zero count=ok out ∧
      out.val=S7Kani3GroupsLoop.model inv.val count.val 0 [] ∧
      out.val.length=count.val := by
  have hlen : flat.val.length ≤ 110 := by omega
  obtain ⟨ps,prod,hprefix,hmodel⟩ := S7Kani2PrefixLoop.prefixes_refines
    flat prefixes product zero flat.val.length hlen (by omega) (by simp [hp]; omega)
  have hps : ps.val.length=flat.val.length := by
    have he := congrArg (fun p : List U32 × U32 => p.1.length) hmodel
    simpa only [hz,List.drop_zero,prefix_length,hp,List.length_nil,Nat.zero_add] using he
  obtain ⟨inv,hinv,_,hinvlen⟩ := S7Kani3InverseLoop.inverse_refines
    flat ps inverse suffix (alloc.vec.Vec.len flat) hlen (by rfl) (by simpa using hps.ge) (by simpa using hi.ge)
  have hilen : inv.val.length=5*count.val := hinvlen.trans (hi.trans hf)
  obtain ⟨out,hout,houtmodel,houtlen⟩ := S7Kani3GroupsLoop.groups_refines
    inv groups zero count count.val hc (by omega) (by omega) (by simp [hg]; omega)
  exact ⟨ps,prod,inv,out,hprefix,hps,hinv,hilen,hout,
    by simpa only [hz,hg] using houtmodel,by simpa only [hg,List.length_nil,Nat.zero_add] using houtlen⟩

#print axioms prefix_length
#print axioms storage_pipeline
end S7Kani3GeometryStorage
