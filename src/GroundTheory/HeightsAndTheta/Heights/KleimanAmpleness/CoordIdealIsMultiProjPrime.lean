module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial

noncomputable section

section Cech

structure CechSystem (ι : Type) (k : Type) [CommRing k] where

  V : Finset ι → Type
  [grp : ∀ I, AddCommGroup (V I)]
  [mod : ∀ I, Module k (V I)]

  res : ∀ {I J : Finset ι}, I ⊆ J → V I →ₗ[k] V J

  piece : ∀ I, Submodule k (V I)

  good : Finset ι → Prop

attribute [instance] CechSystem.grp CechSystem.mod

variable {ι : Type} {k : Type} [CommRing k]

def cechSign [LinearOrder ι] (J : Finset ι) (j : ι) : ℤ := (-1) ^ (J.filter (· < j)).card


open scoped Classical in
open Classical in
def cechD [LinearOrder ι] (C : CechSystem ι k) : (∀ I, C.V I) →ₗ[k] (∀ I, C.V I) :=
  LinearMap.pi fun J => if C.good J then
    ∑ j ∈ J, cechSign J j • ((C.res (Finset.erase_subset j J)).comp (LinearMap.proj (J.erase j)))
  else 0


open scoped Classical in
open Classical in
def cechC (C : CechSystem ι k) (i : ℕ) : Submodule k (∀ I, C.V I) :=
  Submodule.pi Set.univ fun I => if C.good I ∧ I.card = i + 1 then C.piece I else ⊥

def cechZ [LinearOrder ι] (C : CechSystem ι k) (i : ℕ) : Submodule k (∀ I, C.V I) :=
  cechC C i ⊓ LinearMap.ker (cechD C)

def cechB [LinearOrder ι] (C : CechSystem ι k) : ℕ → Submodule k (∀ I, C.V I)
  | 0 => ⊥
  | i + 1 => (cechC C i).map (cechD C)

abbrev cechH [LinearOrder ι] (C : CechSystem ι k) (i : ℕ) : Type :=
  ↥(cechZ C i) ⧸ (cechB C i).comap (cechZ C i).subtype

structure CechHom (C C' : CechSystem ι k) where

  app : ∀ I, C.V I →ₗ[k] C'.V I
  comm : ∀ {I J : Finset ι} (h : I ⊆ J), (C'.res h).comp (app I) = (app J).comp (C.res h)
  piece_le : ∀ I, (C.piece I).map (app I) ≤ C'.piece I
  good_iff : ∀ I, C'.good I ↔ C.good I

variable {C C' : CechSystem ι k}

def CechHom.amb (φ : CechHom C C') : (∀ I, C.V I) →ₗ[k] (∀ I, C'.V I) :=
  LinearMap.pi fun I => (φ.app I).comp (LinearMap.proj I)

theorem CechHom.amb_cechD [LinearOrder ι] (φ : CechHom C C') (v : ∀ I, C.V I) :
    φ.amb (cechD C v) = cechD C' (φ.amb v) := by
  classical
  funext J
  simp only [CechHom.amb, cechD, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  by_cases h : C.good J
  · have h' : C'.good J := (φ.good_iff J).2 h

    simp only [h, h', ite_true, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_zsmul,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← LinearMap.comp_apply, ← φ.comm]
    rfl
  · have h' : ¬ C'.good J := fun h' => h ((φ.good_iff J).1 h')
    simp [h, h']

theorem CechHom.amb_mem_cechC (φ : CechHom C C') {i : ℕ} {v : ∀ I, C.V I} (hv : v ∈ cechC C i) :
    φ.amb v ∈ cechC C' i := by
  classical
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro I
  have hI := hv I
  by_cases h : C.good I ∧ I.card = i + 1
  · have h' : C'.good I ∧ I.card = i + 1 := ⟨(φ.good_iff I).2 h.1, h.2⟩
    simp only [h, h'] at hI ⊢
    exact φ.piece_le I ⟨_, hI, rfl⟩
  · have h' : ¬ (C'.good I ∧ I.card = i + 1) := fun h' => h ⟨(φ.good_iff I).1 h'.1, h'.2⟩
    simp only [h, h', ite_false, Submodule.mem_bot] at hI ⊢
    simp [CechHom.amb, hI]

theorem CechHom.amb_mem_cechB [LinearOrder ι] (φ : CechHom C C') {i : ℕ} {v : ∀ I, C.V I} (hv : v ∈ cechB C i) :
    φ.amb v ∈ cechB C' i := by
  cases i with
  | zero =>
    simp only [cechB, Submodule.mem_bot] at hv ⊢
    simp [hv]
  | succ i =>
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨φ.amb w, φ.amb_mem_cechC hw, (φ.amb_cechD w).symm⟩

def CechHom.Zmap [LinearOrder ι] (φ : CechHom C C') (i : ℕ) : cechZ C i →ₗ[k] cechZ C' i :=
  φ.amb.restrict fun v hv => ⟨φ.amb_mem_cechC hv.1, by
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    rw [← φ.amb_cechD, hv.2, map_zero]⟩

def CechHom.Hmap [LinearOrder ι] (φ : CechHom C C') (i : ℕ) : cechH C i →ₗ[k] cechH C' i :=
  Submodule.mapQ _ _ (φ.Zmap i) fun _ hz => φ.amb_mem_cechB hz

end Cech

section Graded

variable (S : Type) [CommRing S] (N : ℕ)

abbrev Poly : Type := MvPolynomial (Fin (N + 1)) S

def polyPiece (d : ℤ) : Submodule S (Poly S N) :=
  weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) d

structure GradedMod (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] where

  piece : ℤ → Submodule S M
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (d c : ℤ) (f : Poly S N), f ∈ polyPiece S N d → ∀ m ∈ piece c, f • m ∈ piece (d + c)

def denoms (I : Finset (Fin (N + 1))) : Submonoid (Poly S N) :=
  Submonoid.closure ((fun i => (X i : Poly S N)) '' (I : Set (Fin (N + 1))))

theorem denoms_mono {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : denoms S N I ≤ denoms S N J :=
  Submonoid.closure_mono (Set.image_mono (by exact_mod_cast h))

def Xprod (I : Finset (Fin (N + 1))) : Poly S N := ∏ i ∈ I, X i

theorem Xprod_mem_denoms (I : Finset (Fin (N + 1))) : Xprod S N I ∈ denoms S N I :=
  Submonoid.prod_mem _ fun i hi => Submonoid.subset_closure ⟨i, hi, rfl⟩

variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

abbrev LocM (I : Finset (Fin (N + 1))) : Type := LocalizedModule (denoms S N I) M

def locFrac (I : Finset (Fin (N + 1))) (m : M) (n : ℕ) : LocM S N M I :=
  LocalizedModule.mk m ⟨Xprod S N I ^ n, pow_mem (Xprod_mem_denoms S N I) n⟩

def locPiece (G : GradedMod S N M) (I : Finset (Fin (N + 1))) (c : ℤ) : Submodule S (LocM S N M I) :=
  Submodule.span S {y | ∃ (n : ℕ) (m : M), m ∈ G.piece (c + n * I.card) ∧ y = locFrac S N M I m n}

def locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : LocM S N M I →ₗ[S] LocM S N M J :=
  ((LocalizedModule.liftOfLE (denoms S N I) (denoms S N J) (denoms_mono S N h) :
    LocM S N M I →ₗ[Poly S N] LocM S N M J)).restrictScalars S

def gradedSys (G : GradedMod S N M) (c : ℤ) : CechSystem (Fin (N + 1)) S where
  V I := LocM S N M I
  res h := locRes S N M h
  piece I := locPiece S N M G I c
  good I := I.Nonempty

abbrev gradedH (G : GradedMod S N M) (i : ℕ) (c : ℤ) : Type := cechH (gradedSys S N M G c) i

abbrev gradedZ (G : GradedMod S N M) (i : ℕ) (c : ℤ) := cechZ (gradedSys S N M G c) i


open Classical in
def unitCochain (m : M) : ∀ I : Finset (Fin (N + 1)), LocM S N M I :=
  fun I => if I.card = 1 then locFrac S N M I m 0 else 0

variable {M} {M' : Type} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

def IsGradedHom (G : GradedMod S N M) (G' : GradedMod S N M') (f : M →ₗ[Poly S N] M') : Prop :=
  ∀ c, ∀ m ∈ G.piece c, f m ∈ G'.piece c

def locMap (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) : LocM S N M I →ₗ[S] LocM S N M' I :=
  ((IsLocalizedModule.map (denoms S N I) (LocalizedModule.mkLinearMap (denoms S N I) M)
    (LocalizedModule.mkLinearMap (denoms S N I) M') f : LocM S N M I →ₗ[Poly S N] LocM S N M' I)).restrictScalars S

theorem locMap_mk (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) (m : M) (s : denoms S N I) :
    locMap S N f I (LocalizedModule.mk m s) = LocalizedModule.mk (f m) s := by
  simp only [locMap, LinearMap.restrictScalars_apply]
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_locFrac (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) (m : M) (n : ℕ) :
    locMap S N f I (locFrac S N M I m n) = locFrac S N M' I (f m) n :=
  locMap_mk S N f I m _

omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem locRes_mk {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (m : M) (s : denoms S N I) :
    (LocalizedModule.liftOfLE (denoms S N I) (denoms S N J) (denoms_mono S N h)
      (LocalizedModule.mk m s : LocM S N M I)) = LocalizedModule.mk m ⟨(s : Poly S N), denoms_mono S N h s.2⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.liftOfLE_mk' _ _ _ _ _ m s

theorem locRes_comp_locMap (f : M →ₗ[Poly S N] M') {I J : Finset (Fin (N + 1))} (h : I ⊆ J) :
    (locRes S N M' h).comp (locMap S N f I) = (locMap S N f J).comp (locRes S N M h) := by
  refine LinearMap.ext fun y => ?_
  refine LocalizedModule.induction_on (fun m s => ?_) y
  simp only [LinearMap.comp_apply, locRes, LinearMap.restrictScalars_apply]
  rw [locMap_mk, locRes_mk _ _ h, locRes_mk _ _ h, locMap_mk]

theorem locPiece_map_le {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (I : Finset (Fin (N + 1))) (c : ℤ) :
    (locPiece S N M G I c).map (locMap S N f I) ≤ locPiece S N M' G' I c := by
  rw [locPiece, Submodule.map_span_le]
  rintro _ ⟨n, m, hm, rfl⟩
  rw [locMap_locFrac]
  exact Submodule.subset_span ⟨n, f m, hf _ m hm, rfl⟩

def gradedHom {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (c : ℤ) : CechHom (gradedSys S N M G c) (gradedSys S N M' G' c) where
  app I := locMap S N f I
  comm h := locRes_comp_locMap S N f h
  piece_le I := locPiece_map_le S N hf I c
  good_iff _ := Iff.rfl

def gradedHmap {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (i : ℕ) (c : ℤ) : gradedH S N M G i c →ₗ[S] gradedH S N M' G' i c :=
  (gradedHom S N hf c).Hmap i

end Graded

section Cl

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

def chartRingI (x : Fin (N + 1) → Ω) (I : Finset (Fin (N + 1))) : Subalgebra S Ω :=
  Algebra.adjoin S {y | ∃ i ∈ I, ∃ j, y = x j / x i}

theorem chartRingI_singleton (x : Fin (N + 1) → Ω) (i : Fin (N + 1)) :
    chartRingI S x {i} = chartRing S x i := by
  unfold chartRingI chartRing
  congr 1
  ext y
  simp [eq_comm]

variable (E : Type) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

variable {S E}

variable (S)

variable {S}

abbrev LineBundle (x : Fin (N + 1) → Ω) : Type := ChartBundle S x 1 Ω

variable (S)

end Cl

section Filtration

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]


variable {S N}
variable {Ω : Type} [Field Ω] [Algebra S Ω]

variable (S)

end Filtration

section Comparison₂

open ReciprocityTheory.ChartRestriction.G.Geo

variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]


end Comparison₂

section Inhabitants

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] (N : ℕ)

variable {S} {Ω : Type} [Field Ω] [Algebra S Ω]

end Inhabitants

section Inhabitants2

open ReciprocityTheory.ChartRestriction.G.Geo

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]


variable (S N)

end Inhabitants2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
