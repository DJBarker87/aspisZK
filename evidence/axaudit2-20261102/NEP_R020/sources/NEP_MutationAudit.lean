import Lean
import NEP_WALKER
run_cmd NEP.auditModules #[`NEP_Planted, `NEP_Mutations] #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof, `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate, `NEP_MutateProof.proof, `NEP_MutateAux.viaAux] "NEP_Mutation"
