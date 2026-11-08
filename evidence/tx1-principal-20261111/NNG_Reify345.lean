import NNG_ReifyAccounts345
import NNG_ParentAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Reify345
open Aeneas Aeneas.Std NMT_345

/-- Rust carrier facts for the reification lemma only, never a RowSpec domain. -/
def representable (a : RSL.TX1_345.Args) : Prop :=
 a.accounts.length≤Usize.max ∧ a.data.length≤Usize.max ∧
 ∀ acc∈a.accounts,NNG_ReifyAccounts345.representable acc

def input (a : RSL.TX1_345.Args) (h : representable a) : Parent Unit :=
 ⟨LIB_Env.nativeKey a.program_id,
  ⟨a.accounts.map NNG_ReifyAccounts345.raw,by simpa only [List.length_map] using h.1⟩,
  LIBC_Bytes.raw a.data,(),[]⟩

theorem inverse (a : RSL.TX1_345.Args) (h : representable a) :
 NNG_ProjectFrames345.original (input a h)=a := by
 have accounts : (a.accounts.map NNG_ReifyAccounts345.raw).map account=a.accounts := by
  rw [List.map_map]
  calc
   _ = a.accounts.map id := by
    apply List.map_congr_left
    intro acc member
    exact NNG_ReifyAccounts345.source acc (h.2.2 acc member)
   _ = a.accounts := List.map_id _
 unfold NNG_ProjectFrames345.original input
 dsimp only
 rw [NNG_ReifyAccounts345.key_source,accounts,LIBC_Bytes.to_native a.data h.2.1]
 cases a
 rfl
#print axioms inverse

theorem source (a : RSL.TX1_345.Args) (h : representable a) (env : RSL.Env) :
 NNG_Native345.producer (input a h) env=NNG_Model345.interpretation a env := by
 rw [NNG_ParentAssociation345.source,inverse]
#print axioms source
end AspisR1.NNG_Reify345
