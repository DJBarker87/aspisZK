import NPH_R22Callbacks2
import NFS_PacketRoot
import NFS_QueryOps
import NBO_FieldSemantics
import NJJ_QueryOps
import LIBC_QueryOps

/-! NPH_ (R22, step 3, item (iii)): call-site joins on the tx1 (094) query path.

The tx1 query loop runs Port3_NativeQueryBody.verifier.candidate.query_values on the
installed dictionaries of NOC_QueryLink: Dcon = NFS_QueryOps.installed NJJ_QueryOps.concrete
and Dsel = NFS_QueryOps.installed (NFS_CallerDomains.select LIBC_QueryOps.seed). In both,
NFS_QueryOps.installed replaces op2/op3/op9 with NBO_FieldSemantics.add/product/power (the
SelectedMaskProbe QM31 tower), op4–op8 with NBF_BasisInstall (0, 1, and the
Qm31ArithmeticProbe M31 sub, mul and add x x), op16 with SAQ_LineQuery.line and op20 with
FIp_DotsAdapter.dots. The input packet NFS_PacketRoot.Domain carries the canonicality of
alpha[0], alpha[1], the inverses, line_z, the dots inputs g, and the accumulator rhs, power
and rho (NFS_QueryInvariant.Domain). At tx1 it is produced by NOC_QueryDomain.domain on the
57607-byte proof.

Sites discharged here (each kernel call at the site is ok, with canonical or W output):
- node sites, in query_values (`m ← op7 z z; m1 ← op8 m; node ← op6 m1 one`) and in
  accumulate_batched_with_node_loop0.body (`op7 node node; op8; op6 · m`, with m = op5 = 1):
  Qm31ArithmeticProbe M31.mul, M31.add (doubling) and M31.sub, for EVERY input value.
- accumulate tail sites (`op3 value a.power; op2 a.rhs ·; op9 a.power p.rho`): the
  NBO_FieldSemantics product/add/power calls, and through them every SelectedMaskProbe
  QM31/CM31/M31 kernel call inside, on the Domain's canonical rhs/power/rho and a canonical
  value.
- line and circle sites (op16 on alpha[1], op17 on alpha[0]): every CurrentWide kernel call,
  on canonical alpha and canonical values, for any inverse array.
Not discharged here: the value-flow link from the op21/op20 outputs to the NBO tail
`WideCanonical` carrier; the dots internals (FIp_NativeDots); op14 push; the inner basis
loop's update/index bounds (bounds-checked in both profiles). Standard axioms; no ops
interface, merged module or NHV root is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Join094
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Installers AspisR1.NPH_R22Callbacks

abbrev Dcon := AspisR1.NFS_QueryOps.installed NJJ_QueryOps.concrete
abbrev Dsel := AspisR1.NFS_QueryOps.installed (AspisR1.NFS_CallerDomains.select LIBC_QueryOps.seed)

/-- The installed scalar slots of both tx1 query dictionaries. -/
theorem Dcon_scalar :
    Dcon.op5 = ok 1#u32 ∧ Dcon.op6 = AspisR1Qm31ArithmeticProbe.field.M31.sub ∧
    Dcon.op7 = AspisR1Qm31ArithmeticProbe.field.M31.mul ∧
    Dcon.op8 = (fun x => AspisR1Qm31ArithmeticProbe.field.M31.add x x) :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem Dsel_scalar :
    Dsel.op5 = ok 1#u32 ∧ Dsel.op6 = AspisR1Qm31ArithmeticProbe.field.M31.sub ∧
    Dsel.op7 = AspisR1Qm31ArithmeticProbe.field.M31.mul ∧
    Dsel.op8 = (fun x => AspisR1Qm31ArithmeticProbe.field.M31.add x x) :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem Dcon_tail :
    Dcon.op2 = NBO_FieldSemantics.add ∧ Dcon.op3 = NBO_FieldSemantics.product ∧
    Dcon.op9 = NBO_FieldSemantics.power ∧ Dcon.op16 = SAQ_LineQuery.line ∧ Dcon.op17 = FIp_CircleQuery.circle :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem Dsel_tail :
    Dsel.op2 = NBO_FieldSemantics.add ∧ Dsel.op3 = NBO_FieldSemantics.product ∧
    Dsel.op9 = NBO_FieldSemantics.power ∧ Dsel.op16 = SAQ_LineQuery.line ∧ Dsel.op17 = FIp_CircleQuery.circle :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Node sites: mul z z, its doubling, and the subtraction of one are ok for every z. -/
theorem node_sites (z : U32) :
    ∃ m m1 node, AspisR1Qm31ArithmeticProbe.field.M31.mul z z = ok m ∧
      AspisR1Qm31ArithmeticProbe.field.M31.add m m = ok m1 ∧
      AspisR1Qm31ArithmeticProbe.field.M31.sub m1 1#u32 = ok node ∧ W node := by
  obtain ⟨m, hm, vm⟩ := AspisR1.NPH_R22FieldRef.refMul_total z z
  have hm' : AspisR1Qm31ArithmeticProbe.field.M31.mul z z = ok m := by
    rw [AspisR1.NPH_R22FieldCopies.QA_M31_mul_eq]; exact hm
  obtain ⟨m1, hm1, wm1⟩ := QA_add_pres m m (Nat.le_of_lt vm) (Nat.le_of_lt vm)
  obtain ⟨node, hn, wn⟩ := QA_sub_pres m1 1#u32 wm1 (by unfold W; first | decide | simp)
  exact ⟨m, m1, node, hm', hm1, hn, wn⟩

/-- Node sites at the installed slots of Dcon (query_values node and basis loop0 step). -/
theorem Dcon_node_sites (z : U32) :
    ∃ m m1 one node, Dcon.op7 z z = ok m ∧ Dcon.op8 m = ok m1 ∧ Dcon.op5 = ok one ∧
      Dcon.op6 m1 one = ok node ∧ W node := by
  obtain ⟨m, m1, node, h1, h2, h3, w⟩ := node_sites z
  exact ⟨m, m1, 1#u32, node, h1, h2, rfl, h3, w⟩
theorem Dsel_node_sites (z : U32) :
    ∃ m m1 one node, Dsel.op7 z z = ok m ∧ Dsel.op8 m = ok m1 ∧ Dsel.op5 = ok one ∧
      Dsel.op6 m1 one = ok node ∧ W node := by
  obtain ⟨m, m1, node, h1, h2, h3, w⟩ := node_sites z
  exact ⟨m, m1, 1#u32, node, h1, h2, rfl, h3, w⟩

/-- Accumulate tail sites on the query invariant: the three NBO (SelectedMaskProbe tower)
calls are ok with canonical outputs. -/
theorem tail_sites {p start finish a b} (d : AspisR1.NFS_QueryInvariant.Domain p start finish a b)
    (value : SAQ_WideABI.E) (hv : NBO_TailDomain.WideCanonical value) :
    ∃ we we1 q, NBO_FieldSemantics.product value a.power = ok we ∧ NBO_TailDomain.WideCanonical we ∧
      NBO_FieldSemantics.add a.rhs we = ok we1 ∧ NBO_TailDomain.WideCanonical we1 ∧
      NBO_FieldSemantics.power a.power p.rho = ok q ∧ NBF_PowerStep.Canonical q := by
  obtain ⟨we, h1, c1⟩ := NBO_FieldSemantics.product_total value a.power hv d.power
  obtain ⟨we1, h2, c2⟩ := NBO_FieldSemantics.add_total a.rhs we d.rhs c1
  obtain ⟨q, h3, c3⟩ := NBO_FieldSemantics.power_total a.power p.rho d.power d.rho
  exact ⟨we, we1, q, h1, c1, h2, c2, h3, c3⟩

theorem canonE_W (x : SAQ_WideABI.E) (h : Port4C_QueryArithmetic.CanonE x) : WE x := by
  unfold Port4C_QueryArithmetic.CanonE Port3_FlushInstall.Canonical at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := h
  exact ⟨⟨⟨Nat.le_of_lt h1, Nat.le_of_lt h2⟩, ⟨Nat.le_of_lt h3, Nat.le_of_lt h4⟩⟩,
    ⟨⟨Nat.le_of_lt h5, Nat.le_of_lt h6⟩, ⟨Nat.le_of_lt h7, Nat.le_of_lt h8⟩⟩⟩

/-- Line site (op16 = SAQ_LineQuery.line): on a canonical alpha and canonical values every
CurrentWide kernel call succeeds; the output is canonical (SAQ_LineQuery.exact_line). -/
theorem line_site (alpha : SAQ_WideABI.E) (values : Array SAQ_WideABI.E 4#usize) (inverse : Array U32 5#usize)
    (ha : Port4C_QueryArithmetic.CanonE alpha) (hv : ∀ x ∈ values.val, Port4C_QueryArithmetic.CanonE x) :
    ∃ z, SAQ_LineQuery.line alpha values inverse = ok z ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨z, hz, _⟩ := SAQ_LineQuery_line_W alpha values inverse (canonE_W alpha ha) (fun x hx => canonE_W x (hv x hx))
  exact ⟨z, hz, (SAQ_LineQuery.exact_line alpha values inverse z hz).2⟩

/-- Circle site (op17 = FIp_CircleQuery.circle). -/
theorem circle_site (alpha : SAQ_WideABI.E) (values : Array SAQ_WideABI.E 4#usize) (inverse : Array U32 5#usize)
    (ha : Port4C_QueryArithmetic.CanonE alpha) (hv : ∀ x ∈ values.val, Port4C_QueryArithmetic.CanonE x) :
    ∃ z, FIp_CircleQuery.circle alpha values inverse = ok z ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨z, hz, _⟩ := FIp_CircleQuery_circle_W alpha values inverse (canonE_W alpha ha) (fun x hx => canonE_W x (hv x hx))
  exact ⟨z, hz, (FIp_CircleQuery.exact_circle alpha values inverse z hz).2⟩

/-- The two alpha reads of query_values return the Domain's canonical entries. -/
theorem alpha_sites {proof p g geo start finish a b}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b) :
    (∀ w, Array.index_usize p.alpha 0#usize = ok w → Port4C_QueryArithmetic.CanonE w) ∧
    (∀ w, Array.index_usize p.alpha 1#usize = ok w → Port4C_QueryArithmetic.CanonE w) := by
  have hl : p.alpha.val.length = 2 := by first | exact p.alpha.property | simpa using p.alpha.property
  constructor
  · intro w hw
    obtain ⟨t, ht, htv⟩ := WP.spec_imp_exists (Array.index_usize_spec p.alpha 0#usize (by first | scalar_tac | simp [hl] | omega))
    have tw : t = w := Result.ok.inj (ht.symm.trans hw)
    subst tw
    have e : t = p.alpha.val[0]'(by rw [hl]; decide) := by first | (rw [htv]; rfl) | simpa using htv | (subst htv; rfl)
    rw [e]; exact d.alpha0
  · intro w hw
    obtain ⟨t, ht, htv⟩ := WP.spec_imp_exists (Array.index_usize_spec p.alpha 1#usize (by first | scalar_tac | simp [hl] | omega))
    have tw : t = w := Result.ok.inj (ht.symm.trans hw)
    subst tw
    have e : t = p.alpha.val[1]'(by rw [hl]; decide) := by first | (rw [htv]; rfl) | simpa using htv | (subst htv; rfl)
    rw [e]; exact d.alpha1

/-- Composed line site of query_values on the tx1 packet: alpha[1] from the Domain. -/
theorem query_line_site {proof p g geo start finish a b}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b)
    (we6 : SAQ_WideABI.E) (hr : Array.index_usize p.alpha 1#usize = ok we6)
    (values : Array SAQ_WideABI.E 4#usize) (hv : ∀ x ∈ values.val, Port4C_QueryArithmetic.CanonE x)
    (inverse : Array U32 5#usize) :
    ∃ z, Dcon.op16 we6 values inverse = ok z ∧ Port4C_QueryArithmetic.CanonE z :=
  line_site we6 values inverse ((alpha_sites d).2 we6 hr) hv

/-- Composed circle site of query_values on the tx1 packet: alpha[0] from the Domain. -/
theorem query_circle_site {proof p g geo start finish a b}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b)
    (we4 : SAQ_WideABI.E) (hr : Array.index_usize p.alpha 0#usize = ok we4)
    (dots : Array SAQ_WideABI.E 4#usize) (hv : ∀ x ∈ dots.val, Port4C_QueryArithmetic.CanonE x)
    (inverse : Array U32 5#usize) :
    ∃ z, Dcon.op17 we4 dots inverse = ok z ∧ Port4C_QueryArithmetic.CanonE z :=
  circle_site we4 dots inverse ((alpha_sites d).1 we4 hr) hv

/-- Composed accumulate tail sites on the tx1 packet (the query invariant of the Domain). -/
theorem query_tail_sites {proof p g geo start finish a b}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b)
    (value : SAQ_WideABI.E) (hv : NBO_TailDomain.WideCanonical value) :
    ∃ we we1 q, Dcon.op3 value a.power = ok we ∧ NBO_TailDomain.WideCanonical we ∧
      Dcon.op2 a.rhs we = ok we1 ∧ NBO_TailDomain.WideCanonical we1 ∧
      Dcon.op9 a.power p.rho = ok q ∧ NBF_PowerStep.Canonical q :=
  tail_sites d.invariant value hv

#print axioms Dcon_scalar
#print axioms Dsel_scalar
#print axioms Dcon_tail
#print axioms Dsel_tail
#print axioms node_sites
#print axioms Dcon_node_sites
#print axioms Dsel_node_sites
#print axioms tail_sites
#print axioms canonE_W
#print axioms line_site
#print axioms circle_site
#print axioms alpha_sites
#print axioms query_line_site
#print axioms query_circle_site
#print axioms query_tail_sites
end AspisR1.NPH_R22Join094
