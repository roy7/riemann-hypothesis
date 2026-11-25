module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
public import Mathlib.RingTheory.Noetherian.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def SerreVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH S N M G i c)

section Inhabitants

variable (k : Type) [Field k]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
