import R1Z.ProverCommitAudit49
import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Eval50
import AspisR1ProducerRelease47.Linear50
import AspisR1ProducerRelease47.MaskFinish50
import AspisR1ProducerRelease47.MaskHorner50
import AspisR1ProducerRelease47.Mle50
import AspisR1ProducerRelease47.Prepared50
import AspisR1ProducerRelease47.Run50
import AspisR1ProducerRelease47.Sparse50
import AspisR1ProducerRelease47.SparseScan50
import AspisR1ProducerRelease47.SparseSum50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Tower50
import R1Z.ProverCommitDot50
import R1Z.ProverCommitEval50
import R1Z.ProverCommitEvalBlock50
import R1Z.ProverCommitEvalLoop50
import R1Z.ProverCommitHornerMath50
import R1Z.ProverCommitLinear50
import R1Z.ProverCommitLinearLoop50
import R1Z.ProverCommitLinearMath50
import R1Z.ProverCommitMaskCoefficients50
import R1Z.ProverCommitMaskFinish50
import R1Z.ProverCommitMaskHorner50
import R1Z.ProverCommitMaskPolynomial50
import R1Z.ProverCommitMle50
import R1Z.ProverCommitPrepare50
import R1Z.ProverCommitPrepared50
import R1Z.ProverCommitPreparedCM50
import R1Z.ProverCommitRadix50
import R1Z.ProverCommitRadixField50
import R1Z.ProverCommitRadixTop50
import R1Z.ProverCommitScale50
import R1Z.ProverCommitSparse50
import R1Z.ProverCommitSparseAddress50
import R1Z.ProverCommitSparseBits50
import R1Z.ProverCommitSparseConcat50
import R1Z.ProverCommitSparseDense50
import R1Z.ProverCommitSparseEnum50
import R1Z.ProverCommitSparseOutput50
import R1Z.ProverCommitSparseParams50
import R1Z.ProverCommitSparsePredicate50
import R1Z.ProverCommitSparseProduct50
import R1Z.ProverCommitSparseRows50
import R1Z.ProverCommitSparseSplit50
import R1Z.ProverCommitSparseSuffix50
import R1Z.ProverCommitSparseSum50
import R1Z.ProverCommitSparseWeight50
import R1Z.ProverCommitSparseWidth50
import R1Z.ProverCommitTotals50
import R1Z.ProverCommitTower50
import R1Z.ProverCommitTowerModel50
import R1Z.ProverCommitDeployedFuel22
/-! One coherent import/axioms audit of the accepted part-50 cone.
No complete simulator payload or frozen-manifest release claim is made. -/
#print axioms R1Z.ProverCommitDot50.prepare3
#print axioms R1Z.ProverCommitDot50.exact_result
#print axioms R1Z.ProverCommitEval50.exact_result
#print axioms R1Z.ProverCommitEvalBlock50.index
#print axioms R1Z.ProverCommitEvalBlock50.block
#print axioms R1Z.ProverCommitEvalLoop50.go
#print axioms R1Z.ProverCommitHornerMath50.eval_succ
#print axioms R1Z.ProverCommitHornerMath50.top
#print axioms R1Z.ProverCommitLinear50.form0
#print axioms R1Z.ProverCommitLinear50.form16
#print axioms R1Z.ProverCommitLinear50.chain
#print axioms R1Z.ProverCommitLinear50.forms
#print axioms R1Z.ProverCommitLinear50.power26
#print axioms R1Z.ProverCommitLinearLoop50.go
#print axioms R1Z.ProverCommitLinearMath50.stats_value
#print axioms R1Z.ProverCommitLinearMath50.sum_fin
#print axioms R1Z.ProverCommitLinearMath50.weighted_fin
#print axioms R1Z.ProverCommitLinearMath50.form
#print axioms R1Z.ProverCommitMaskCoefficients50.outside
#print axioms R1Z.ProverCommitMaskCoefficients50.reconstruct
#print axioms R1Z.ProverCommitMaskCoefficients50.eval_mask
#print axioms R1Z.ProverCommitMaskFinish50.exact_result
#print axioms R1Z.ProverCommitMaskHorner50.go
#print axioms R1Z.ProverCommitMaskHorner50.exact_result
#print axioms R1Z.ProverCommitMaskPolynomial50.eval_shared
#print axioms R1Z.ProverCommitMaskPolynomial50.eval_mask
#print axioms R1Z.ProverCommitMaskPolynomial50.factor_ne_23
#print axioms R1Z.ProverCommitMaskPolynomial50.mask_only_ne_23
#print axioms R1Z.ProverCommitMaskPolynomial50.omitted_23
#print axioms R1Z.ProverCommitMle50.exact_result
#print axioms R1Z.ProverCommitMle50.dense_dot
#print axioms R1Z.ProverCommitMle50.model_result
#print axioms R1Z.ProverCommitPrepare50.triple_array
#print axioms R1Z.ProverCommitPrepare50.cm
#print axioms R1Z.ProverCommitPrepare50.q
#print axioms R1Z.ProverCommitPrepared50.prepare_eq
#print axioms R1Z.ProverCommitPrepared50.prepare
#print axioms R1Z.ProverCommitPrepared50.combine
#print axioms R1Z.ProverCommitPrepared50.karatsuba
#print axioms R1Z.ProverCommitPrepared50.mul
#print axioms R1Z.ProverCommitPrepared50.caller
#print axioms R1Z.ProverCommitPreparedCM50.cm
#print axioms R1Z.ProverCommitRadix50.eval_poly
#print axioms R1Z.ProverCommitRadix50.block_sum
#print axioms R1Z.ProverCommitRadix50.blocks_poly
#print axioms R1Z.ProverCommitRadixField50.top
#print axioms R1Z.ProverCommitRadixTop50.top
#print axioms R1Z.ProverCommitScale50.scale
#print axioms R1Z.ProverCommitSparse50.eqwB_product
#print axioms R1Z.ProverCommitSparse50.boolean_weight
#print axioms R1Z.ProverCommitSparse50.prune
#print axioms R1Z.ProverCommitSparseAddress50.bound
#print axioms R1Z.ProverCommitSparseAddress50.row
#print axioms R1Z.ProverCommitSparseBits50.condition
#print axioms R1Z.ProverCommitSparseBits50.factor
#print axioms R1Z.ProverCommitSparseConcat50.bound
#print axioms R1Z.ProverCommitSparseConcat50.high
#print axioms R1Z.ProverCommitSparseConcat50.low
#print axioms R1Z.ProverCommitSparseConcat50.bits
#print axioms R1Z.ProverCommitSparseDense50.dense_sparse
#print axioms R1Z.ProverCommitSparseEnum50.injective
#print axioms R1Z.ProverCommitSparseEnum50.bijective
#print axioms R1Z.ProverCommitSparseEnum50.sum_concat
#print axioms R1Z.ProverCommitSparseEnum50.append_weight
#print axioms R1Z.ProverCommitSparseEnum50.prune
#print axioms R1Z.ProverCommitSparseOutput50.total_fin
#print axioms R1Z.ProverCommitSparseOutput50.exact_result
#print axioms R1Z.ProverCommitSparseParams50.count
#print axioms R1Z.ProverCommitSparseParams50.parameters
#print axioms R1Z.ProverCommitSparsePredicate50.one_result
#print axioms R1Z.ProverCommitSparsePredicate50.boolean_result
#print axioms R1Z.ProverCommitSparsePredicate50.one_iff
#print axioms R1Z.ProverCommitSparsePredicate50.boolean_iff
#print axioms R1Z.ProverCommitSparsePredicate50.boolean_value
#print axioms R1Z.ProverCommitSparseProduct50.product_fin
#print axioms R1Z.ProverCommitSparseProduct50.full_weight
#print axioms R1Z.ProverCommitSparseRows50.row
#print axioms R1Z.ProverCommitSparseSplit50.split_weight
#print axioms R1Z.ProverCommitSparseSplit50.prune
#print axioms R1Z.ProverCommitSparseSuffix50.append_val
#print axioms R1Z.ProverCommitSparseSuffix50.suffix
#print axioms R1Z.ProverCommitSparseSum50.sum
#print axioms R1Z.ProverCommitSparseWeight50.weight
#print axioms R1Z.ProverCommitSparseWidth50.width
#print axioms R1Z.ProverCommitTotals50.array3
#print axioms R1Z.ProverCommitTotals50.channel
#print axioms R1Z.ProverCommitTotals50.all
#print axioms R1Z.ProverCommitTower50.cm_i
#print axioms R1Z.ProverCommitTower50.mul
#print axioms R1Z.ProverCommitTowerModel50.basis_model
#print axioms R1Z.ProverCommitTowerModel50.exact_result
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
