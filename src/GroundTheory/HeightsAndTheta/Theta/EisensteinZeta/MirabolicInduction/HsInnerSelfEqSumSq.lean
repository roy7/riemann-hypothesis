module

public import GroundTheory.AutomorphicForms.RealGroupsLie
public import Mathlib.Analysis.CStarAlgebra.Matrix

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements, GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq

-- ===== clump member: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements", "h": "module\n\npublic import GroundTheory.AutomorphicForms.RealGroupsLie\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace SecondKind

abbrev MatProd {f : ℕ} (p q : Fin f → ℕ) : Type :=
  (τ : Fin f) → Matrix (Fin (p τ) ⊕ Fin (q τ)) (Fin (p τ) ⊕ Fin (q τ)) ℂ

def lieProd {f : ℕ} (p q : Fin f → ℕ) : Submodule ℝ (MatProd p q) :=
  Submodule.pi Set.univ fun τ => indefiniteUnitaryLieAlgebra (p τ) (q τ)

def hsInner {f : ℕ} {p q : Fin f → ℕ} (X X' : MatProd p q) : ℝ :=
  ∑ τ, (trace (X τ * (X' τ)ᴴ)).re

structure OrthoFrame where

  f : ℕ

  r : ℕ
  f_pos : 1 ≤ f
  r_pos : 1 ≤ r

  p : Fin f → ℕ

  q : Fin f → ℕ
  sig : ∀ τ, p τ + q τ = r

  place : Fin (f * r ^ 2) → Fin f

  E : Fin (f * r ^ 2) → MatProd p q
  span : Submodule.span ℝ (Set.range E) = lieProd p q
  orthonormal : ∀ k l, hsInner (E k) (E l) = if k = l then 1 else 0
  supp : ∀ l τ, τ ≠ place l → E l τ = 0

namespace OrthoFrame

variable (F : OrthoFrame)

end OrthoFrame

end SecondKind

end

end GroundTheory.Heights₂.Theta
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport GroundTheory.AutomorphicForms.RealGroupsLie\npublic import GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

end

end GroundTheory.Heights₂.Theta
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq =====
