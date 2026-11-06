import NKP_LaneInduction
set_option autoImplicit false
noncomputable section
namespace NKP_LaneCarrier
open Aeneas Aeneas.Std Result
abbrev Node := NKP_LaneCuts.Node
abbrev Frontier := NKP_LaneCuts.Frontier
abbrev Lane := NKF_LaneConstructor.Lane
abbrev Word := AdapterRw.aspis_core.field.M31
/-- Value representation only: no numeric normalization or empty-root table
is evaluated. The native constructor uses the corresponding fixed arrays. -/
def node (words : Node) : Array Word 8#usize :=
 ⟨List.ofFn words, by simp⟩
def frontier (state : Frontier) : Array (Array Word 8#usize) 20#usize :=
 ⟨List.ofFn (fun level => node (state level)), by simp⟩

theorem node_at (words : Node) (word : Fin 8) :
 (node words).val[word.val]? = some (words word) := by
 change (List.ofFn words)[word.val]? = some (words word)
 simp only [List.getElem?_ofFn,dif_pos word.isLt]

theorem frontier_at (state : Frontier) (level : Fin 20) :
 (frontier state).val[level.val]? = some (node (state level)) := by
 change (List.ofFn (fun i => node (state i)))[level.val]? = some (node (state level))
 simp only [List.getElem?_ofFn,dif_pos level.isLt]

/-- Exact canonical owned record built at the frozen lane constructor.
This bridges the functional one-iteration carrier to AdapterRw's array
carrier; the source header/root-decoder packet remains a separate obligation. -/
def make (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root : Node) (state : Frontier) : Lane :=
 ⟨bump,master,lane,⟨next,node root,frontier state⟩⟩

theorem root_at (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root : Node) (state : Frontier) (word : Fin 8) :
 (make bump master lane next root state).tree.root.val[word.val]? = some (root word) :=
 node_at root word

theorem frontier_row (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root : Node) (state : Frontier) (level : Fin 20) :
 (make bump master lane next root state).tree.frontier.val[level.val]? =
 some (node (state level)) := frontier_at state level

/-- All returned native constructor windows determine this SAME canonical
record. The proposition is the six named constructor observations, and record
identity is derived by the predecessor's extensionality proof. -/
theorem returned (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root : Node) (state : Frontier) (out : Lane)
 (cut : NKF_LaneConstructor.Fields (make bump master lane next root state) out) :
 out = make bump master lane next root state :=
 (NKF_LaneConstructor.constructor _ _ cut).symm

#print axioms node_at
#print axioms frontier_at
#print axioms root_at
#print axioms frontier_row
#print axioms returned
end NKP_LaneCarrier
