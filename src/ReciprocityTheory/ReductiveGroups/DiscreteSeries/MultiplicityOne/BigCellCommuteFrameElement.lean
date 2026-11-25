module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow, ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow", "h": "module\n\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed\npublic import Formalism.HermitianCurvature.WeylElementCommutesLevelOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one, Pi.single_apply] at this
  exact this

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e := congrFun (congrFun hU' c) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c] at e
  · rw [conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul, hpk_mul_apply, hpk_row] at e
    have hs : sgn k r c ≠ 0 := by
      intro h0
      have := sgn_mul_self (k := k) (r := r) c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    by_cases hj : j = tau k r c
    · rw [if_pos hj] at e
      rw [if_pos hj.symm]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [if_neg hj] at e
      rw [if_neg (Ne.symm hj)]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro p _ hp
    rw [conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  by_cases hcr : c.val < r
  · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
    have := (hh.2.1 ⟨c.val, hcr⟩).1
    rw [e] at this
    exact col_of_fix this p
  · have ha : 2 * r + k - c.val < r := by omega
    have e : esI k r ⟨2 * r + k - c.val, ha⟩ = c := by
      apply Fin.ext
      simp only [esI]
      omega
    have := (hh.2.1 ⟨2 * r + k - c.val, ha⟩).2
    rw [e] at this
    exact col_of_fix this p

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  unfold tau
  simp only
  split_ifs
  omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have := row_of_fixed_col hh.1 (tau k r i) (uw_fixed_col hh _ (tau_out i hi)) j
  rw [tau_tau] at this
  exact this

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  have hu := isUnit_of_uh hh.1
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hh.1, fun a => ⟨fix _ (hh.2.1 a).1, fix _ (hh.2.1 a).2⟩, fix _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  refine ⟨uh_mul hh.1 hh'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).1, (hh.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).2, (hh.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hh'.2.2, hh.2.2]

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hcol, if_pos rfl, mul_one]
  · intro q _ hq
    rw [hcol, if_neg hq, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem ell_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold ell
  apply Finset.sum_congr rfl
  intro a _
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dite_eq_right (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dite_eq_right (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dite_eq_left ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  apply Formalism.FourierDecayAlt.P.B2x3.Em_mul_mid <;> assumption

lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  apply Formalism.FourierDecayAlt.P.B2x3.mul_EmT_mid <;> assumption

lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  apply Formalism.FourierDecayAlt.P.B2x3.EmT_Em

lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  apply Formalism.FourierDecayAlt.P.B2x3.emb_eq

lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  apply Formalism.FourierDecayAlt.P.B2x3.sandwich <;> assumption

lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  have h := sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.mul_one] at h
  rw [h, emb_eq, Matrix.mul_one, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement", "h": "module\n\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

lemma Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)
  calc Hb k * γᴴ * Hb k * γ = Hb k * (γᴴ * Hb k * γ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hb_mul_self]

lemma emb_inv {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    (embWb k r γ)⁻¹ = embWb k r γ⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

lemma emb_unit {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) : IsUnit (embWb k r γ).det :=
  Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

section gbar

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  unfold gbar
  have e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [e, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  apply ReciprocityTheory.ChartRestriction.DS.Mult1.InvGrp.gbar_gbar <;> assumption

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det :=
  Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)

lemma th_five {a b g c d : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (hg : th k r γ g = g) :
    th k r γ (a⁻¹ * b⁻¹ * g * c * d) =
      (gbar k r γ d)⁻¹ * (gbar k r γ c)⁻¹ * g * gbar k r γ b * gbar k r γ a := by
  unfold th at hg ⊢
  rw [gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha),
    Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]

lemma th_mul_inv {h h' : Mat k r} (hh' : IsUnit h'.det) :
    th k r γ (h * h'⁻¹) = gbar k r γ h' * (gbar k r γ h)⁻¹ := by
  unfold th
  rw [gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]

end gbar

lemma psi_conj (z : Fin (2 * r + k + 1) → ℂ) {a : Mat k r} (ha : a ∈ UWset k r z) (c : ℂ) (n : Mat k r) :
    psi k r z c (a * n * a⁻¹) = psi k r z c n := by
  unfold psi
  rw [ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]

lemma tau_wI (j : Fin (k + 1)) : tau k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold tau wI
  apply Fin.ext
  simp only
  split_ifs with h <;> omega

lemma mud_off (d : ℂ) (x y : Fin (k + 1)) (h : (x ≠ 0 ∧ x ≠ Fin.last k) ∨ (y ≠ 0 ∧ y ≠ Fin.last k)) :
    mud k d x y = if x = y then 1 else 0 := by
  unfold mud
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

lemma emb_mud_off (d : ℂ) (i j : Fin (2 * r + k + 1))
    (h : (i ≠ wI k r 0 ∧ i ≠ wI k r (Fin.last k)) ∨ (j ≠ wI k r 0 ∧ j ≠ wI k r (Fin.last k))) :
    embWb k r (mud k d) i j = if i = j then 1 else 0 := by
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ i j hi hj, mud_off]
      · by_cases e : i = j
        · subst e; simp
        · rw [if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩
        · right
          exact ⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩
    · exact emb_out_col _ i j hj
  · exact emb_out_row _ i j hi

lemma comm_mud (hk : 1 ≤ k) {R : Mat k r} (hR : R ∈ UH (Hpk k r))
    (h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)) (hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (d : ℂ) : R * embWb k r (mud k d) = embWb k r (mud k d) * R := by
  set a := wI k r 0
  set b := wI k r (Fin.last k)
  have hne : a ≠ b := fun h => by
    have := congrArg Fin.val (wI_inj h)
    simp at this
    omega
  have c0 := col_of_fix h0
  have cL := col_of_fix hL
  have r0 : ∀ j, R a j = if a = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR a c0 j
    rwa [tau_wI] at this
  have rL : ∀ j, R b j = if b = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR b cL j
    rwa [tau_wI] at this
  set P : Mat k r := embWb k r (mud k d) - 1 with hPdef
  have hM : embWb k r (mud k d) = 1 + P := by rw [hPdef]; abel
  have hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0 := by
    intro i j h
    rw [hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]
  have RP : R * P = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]),
      c0, cL]
    by_cases ha : i = a
    · subst ha; rw [if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]
    · by_cases hb : i = b
      · subst hb; rw [if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]
      · rw [if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]
  have PR : P * R = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]),
      r0, rL]
    by_cases ha : j = a
    · subst ha; rw [if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]
    · by_cases hb : j = b
      · subst hb; rw [if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]
      · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]

lemma big_cell_commute_frame_element (hBCF : BigCellFactor) (hUWb : UWbFacts) (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ}
    {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsZFrame k r z γ) {u : Mat k r} (hu : u ∈ UUset k r z γ)
    (c : Fin r → ℂ) (d : ℂ) : u * g0 k r γ c d = g0 k r γ c d * u := by
  have hγu := unit_of_frame hγ.1
  have hEu : IsUnit (embWb k r γ).det := emb_unit hγu
  have hEW : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
  have hEG : embWb k r γ ∈ UH (Hpk k r) := hEW.1
  have huW : u ∈ UWb k r := (hUWb k r).2.1 z hu.1
  set E := embWb k r γ with hEdef
  set R := E⁻¹ * u * E with hRdef
  have hR : R ∈ UH (Hpk k r) := uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG
  have fixR : ∀ v, E *ᵥ v = v → True := fun _ _ => trivial
  have h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _
    rw [hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hRM := comm_mud hk hR h0 hL d
  have hu' : u = E * R * E⁻¹ := by
    rw [hRdef]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu,
      Matrix.mul_one]
  have key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u := by
    rw [hu']
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]
    rw [← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]
  unfold g0
  rw [(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]
  have hc := (hUWb k r).2.2 c u huW
  calc u * (bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹))
      = bigCell k r c 1 * (u * (E * embWb k r (mud k d) * E⁻¹)) := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    _ = bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹) * u := by rw [key]; simp only [Matrix.mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement =====
