import Lean
import R1QueryFirstRead
import R1QueryDecoder
import R1QueryCompletionSupport
import R0C.V3.BSOk
import R0C.ModuloCounting
import WideTower
import R0C.ModuloField
import Wide.InitialEncoder
import Wide.FinalEncoder
import R0.Fold
import Wide.EncoderLinearity
import R0.PolynomialPair
import R0.ChordDegree
import R0.Dot
import R0.RoundNormalization
import R0.RoundCore
import R0.Round
import R0.LinearDual
import R0.ChordImage
import R0.ChordGeometry
import R0.Chord
import R0.FunctionalWeights
import R0.ResponseSelection
import Wide.BatchSeparation
import Wide.GRSConversion
import Wide.MultiplicityThreeGS
import Wide.Cardinality
import Wide.JointList
import Wide.DegreeThreeMatched
import Wide.Interpolation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1QueryFirstRead, `R1QueryDecoder, `R1QueryCompletionSupport, `R0C.V3.BSOk, `R0C.ModuloCounting, `WideTower, `R0C.ModuloField, `Wide.InitialEncoder, `Wide.FinalEncoder, `R0.Fold, `Wide.EncoderLinearity, `R0.PolynomialPair, `R0.ChordDegree, `R0.Dot, `R0.RoundNormalization, `R0.RoundCore, `R0.Round, `R0.LinearDual, `R0.ChordImage, `R0.ChordGeometry, `R0.Chord, `R0.FunctionalWeights, `R0.ResponseSelection, `Wide.BatchSeparation, `Wide.GRSConversion, `Wide.MultiplicityThreeGS, `Wide.Cardinality, `Wide.JointList, `Wide.DegreeThreeMatched, `Wide.Interpolation]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
