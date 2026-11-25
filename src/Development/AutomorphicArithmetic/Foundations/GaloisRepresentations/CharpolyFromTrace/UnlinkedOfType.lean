module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {Γ I : Type} [Group Γ] [Group I] {a c : ℕ}

end Abstract

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

end Global

def DenseFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite →
    Dense {g : G E Ω | ∃ u, IsSplitAt u ∧ u ∉ S ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ IsFrob A (normV u) g⁻¹}

def UnrField : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ f : ℕ, 0 < f → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → normV w' = normV w ^ f) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ

def IneNorm : Prop :=
  ∀ (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω]
    [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] (h : IsPlaceOver A v) (h' : IsPlaceOver A w),
    (∀ t ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) M t) → ∀ art art', IsLocalArtin h art → IsLocalArtin h' art' →
    ∃ g : ↥(Ine (F := E) A) ≃* ↥(Ine (F := M) A), (∀ s, UpperTheory.V.Af.Bc.res E Ω M (g s : G M Ω) = s) ∧
      ∀ s, art (ineIncl h s) = GlobalTheory.BCChar.normU v w (art' (ineIncl h' (g s)))

end UpperTheory.Gal.NearKilling
