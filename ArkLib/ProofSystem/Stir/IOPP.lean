/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.OracleReduction.Security.Basic
import Mathlib.Tactic


namespace Reduction
open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {ι : Type}

section IOPP

-- Quang: this should really be in the main `OracleReduction` namespace
-- i.e. the idea of bundling a protocol with its security definitions

/-- An *interactive-oracle proof of proximity* (IOPP) is an
    Interactive oracle proof enriched with three security properties
    of (perfect) completeness, soundness and round-by-round soundness.-/
structure IOPP
    (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [∀ i, VCVCompatible (pSpec.Challenge i)][oSpec.FiniteRange]
    [∀ i, ToOracle (pSpec.Message i)]
    (StmtIn WitIn : Type)
    { ιₛₒ: Type} (OStmtIn : ιₛₒ → Type)[∀ i, ToOracle (OStmtIn i)]
    (ε_rbr : pSpec.ChallengeIndex → ℝ≥0)
    where

  /-- The underlying interactive-oracle proof-/
  iop : OracleProof pSpec oSpec StmtIn WitIn OStmtIn

  /-- The input relation on the input statement, the input oracle statement(s), and the input
    witness -/
  oRelIn : StmtIn × (∀ i, OStmtIn i) → WitIn → Prop

  /-- The output relation on the boolean output (accept/reject), the empty output oracle statement,
    and the trivial output witness -/
  oRelOut : Bool × (∀ _ : Empty, Unit) → Unit → Prop

  /-- The IOPP satisfies perfect completeness -/
  ioppCompleteness : iop.perfectCompleteness oRelIn oRelOut

  /-- The state function for the IOPP, define with regards to the languages of the input and output
    relations, and the IOPP's verifier (seen as a regular verifier) -/
  stateFn : StateFunction oRelIn.language oRelOut.language iop.verifier.toVerifier

  /-- The IOPP satisfies round-by-round soundness with respect to the state function and to the rbr
    knowledge error `ε_rbr` -/
  ioppRBRKnowledgeSoundness : OracleReduction.rbrKnowledgeSoundness
    oRelIn oRelOut iop.verifier stateFn ε_rbr

end IOPP
end Reduction
