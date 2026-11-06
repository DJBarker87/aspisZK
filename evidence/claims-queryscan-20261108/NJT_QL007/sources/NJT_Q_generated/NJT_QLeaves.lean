import NJT_QBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QLeaves
open Aeneas Aeneas.Std Result NJT_QBase

/-- Reviewed transcription of NJT_Q_block_rank: for arbitrary input block and
arbitrary k<8, out[k] is the four source bytes in little endian order.
The KMX/control association and source hashes are in NJT_QCERTIFICATES.md. -/
def RankCut (b : Bytes) (out : Words) : Prop :=
 ∀ k : Fin 8, out.val[k.val]'(by have h:=out.property;change out.val.length=8 at h;omega)=
  (rank b).val[k.val]'(by simp [rank];exact k.isLt)

/-- Reviewed transcription of NGQ_query_words, NGQ_K042/043: every arbitrary
window equals the ordered source little endian word masked by 262143. -/
def WordsCut (b : Bytes) (out : Words) : Prop :=
 ∀ k : Fin 8, out.val[k.val]'(by have h:=out.property;change out.val.length=8 at h;omega)=
  (words b).val[k.val]'(by simp [words];exact k.isLt)

/-- Exact Result cases asserted by NGQ_finish, NGQ_K004/005. Its arbitrary
window is universally instantiated here; no successful finish is assumed. -/
def FinishCut (s : State) (out : Finish) : Prop :=
 match out with
 | .Ok q => s.accepted_len=22#usize ∧ ∀ k : Fin 22,
  q.val[k.val]'(by have h:=q.property;change q.val.length=22 at h;omega)=
   s.accepted.val[k.val]'(by have h:=s.accepted.property;change s.accepted.val.length=22 at h;omega)
 | .Err (.DrawLimitExhausted n d) => s.accepted_len≠22#usize ∧ n=s.accepted_len ∧ d=64#usize
 | .Err _ => False

theorem array_window {n : Usize} (a b : Array U32 n)
 (windows : ∀ k : Fin n.val,
  a.val[k.val]'(by have h:=a.property;omega)=b.val[k.val]'(by have h:=b.property;omega)) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact a.property.trans b.property.symm
 · intro i ha hb
   exact windows ⟨i,by have h:=a.property;omega⟩

/-- TX1:068 root. Only the reviewed native window cut is a Prop input. -/
theorem block_rank (b : Bytes) (out : Words) (native : RankCut b out) :
 AspisR1QueryScanUnrolled.r0_transcript.block_rank b=ok out := by
 have eq : out=rank b:=array_window _ _ native
 rw [eq]
 exact rank_source b

/-- TX1:070 root. The native body executes its real block_rank child. -/
theorem query_words (b : Bytes) (out : Words) (native : WordsCut b out) :
 Query31ConcreteWordsDriverChain.actualQueryWords b=ok out := by
 have eq : out=words b:=array_window _ _ native
 rw [eq]
 exact words_source b

/-- TX1:066 root. All Result arms and all22 returned cells; source is pure. -/
theorem finish (s : State) (out : Finish) (native : FinishCut s out) :
 AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s=ok out := by
 have eq : out=NJT_QBase.finish s := by
  cases out with
  | Ok q =>
   obtain ⟨full,cells⟩:=native
   have arr : q=s.accepted:=array_window _ _ cells
   simp only [NJT_QBase.finish,full,if_true,arr]
  | Err error =>
   cases error with
   | BoundNotPowerOfTwo n => exact False.elim native
   | CountExceedsBound n b => exact False.elim native
   | DrawLimitExhausted n d =>
    obtain ⟨notfull,hn,hd⟩:=native
    simp only [NJT_QBase.finish,notfull,if_false,hn,hd]
 rw [eq]
 exact finish_source s

#print axioms array_window
#print axioms block_rank
#print axioms query_words
#print axioms finish
#check @block_rank
#check @query_words
#check @finish
end AspisR1.NJT_QLeaves
end
