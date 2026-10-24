"""Apply narrowly scoped experimental type transport to a job-owned source copy.

This patch is unadopted. Its operation checks and extraction remain release
obligations; successful OCaml compilation is not a source-association proof.
"""
from pathlib import Path
import subprocess

D = Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
S = D/'base/src'
assert not (D/'candidate-applied').exists()

def replace(rel, before, after, count=1):
    p = S/rel
    text = p.read_text()
    assert text.count(before) == count, (rel, before, text.count(before))
    p.write_text(text.replace(before, after))

replace('llbc/TypesUtils.ml', 'include Charon.TypesUtils\n', '''include Charon.TypesUtils

(* ProverRwRngExtractor: an exact refined scalar, never an I32 alias.
   No range reordering, generalized pattern or unchecked constructor support. *)
let prover_rw_nonzero_i32_pattern (ty : ty) : bool =
  let bound (c : constant_expr) expected =
    match (c.ty, c.kind) with
    | TLiteral (TInt I32), CLiteral (Values.VScalar (Values.SignedScalar (I32, n))) ->
        Z.equal n (Z.of_string expected)
    | _ -> false
  in
  match ty with
  | TPattern (TLiteral (TInt I32), OrPattern [Range (a,b); Range (c,d)]) ->
      bound a "-2147483648" && bound b "-1" && bound c "1" && bound d "2147483647"
  | _ -> false
''')
replace('pure/Pure.ml', '  | TLiteral of literal_type\n', '''  | TLiteral of literal_type
  | TProverRwNonZeroI32
      (** Experimental exact I32 nonzero refinement. No literal constructor,
          projection, cast or implicit coercion exists for this node. *)
''')
replace('llbc/TypesAnalysis.ml', '    | TLiteral _ | TNever | TDynTrait _ -> ty_info', '''    | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> ty_info
    | TLiteral _ | TNever | TDynTrait _ -> ty_info''')
# This second traversal's argument is named [ty].
replace('llbc/TypesAnalysis.ml', '        | TVar _ | TLiteral _ | TNever -> ()', '''        | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> ()
        | TVar _ | TLiteral _ | TNever -> ()''')
replace('symbolic/SymbolicToPureTypes.ml', '  | TLiteral ty -> TLiteral (translate_literal_type ty)', '''  | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> TProverRwNonZeroI32
  | TLiteral ty -> TLiteral (translate_literal_type ty)''')
replace('symbolic/SymbolicToPureTypes.ml', '  | TLiteral lty -> TLiteral (translate_literal_type lty)', '''  | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> TProverRwNonZeroI32
  | TLiteral lty -> TLiteral (translate_literal_type lty)''')
replace('symbolic/SymbolicToPureTypes.ml', '    | TVar _ | TNever | TLiteral _ -> save_count outer_regions', '''    | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> save_count outer_regions
    | TVar _ | TNever | TLiteral _ -> save_count outer_regions''')
replace('symbolic/SymbolicToPureTypes.ml', '    | TVar _ | TNever | TLiteral _ -> stop outer_regions ty', '''    | TPattern _ when TypesUtils.prover_rw_nonzero_i32_pattern ty -> stop outer_regions ty
    | TVar _ | TNever | TLiteral _ -> stop outer_regions ty''')
replace('pure/PrintPure.ml', '  | TLiteral lty -> literal_type_to_string lty', '''  | TProverRwNonZeroI32 -> "ProverRwRngExtractor.NonZeroI32"
  | TLiteral lty -> literal_type_to_string lty''')
replace('extract/ExtractBase.ml', '      | TNever | TError -> "x"', '''      | TProverRwNonZeroI32 -> "nz"
      | TNever | TError -> "x"''')
replace('extract/ExtractTypes.ml', '  | TLiteral lty -> extract_literal_type ctx fmt lty', '''  | TProverRwNonZeroI32 ->
      [%cassert] span (Config.backend () = Lean)
        "ProverRwRngExtractor refined I32 supports only Lean";
      F.pp_print_string fmt "{ x : I32 // x.val ≠ 0 }"
  | TLiteral lty -> extract_literal_type ctx fmt lty''')
(D/'candidate-applied').write_text('Experimental type node only; operation preflight not yet validated.\n')
print('Applied experimental refined scalar type transport; not adopted')
