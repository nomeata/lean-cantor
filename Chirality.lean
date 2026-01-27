/-
# Chirality.lean
# Chiral Decomposition and Grade-Halving for Cantor Space

This module formalizes the key discovery from the GA translation:
**The `branch` function performs chiral decomposition that halves the effective grade.**

## Main Results

1. `chiral_decomposition`: Every Cantor sequence decomposes into chirality + left + right
2. `surface_moduli_lt`: Both surface moduli are strictly less than n for n ≥ 2
3. Position lemmas for branch

## The Key Insight

```
Original:  p with modulus n
After branch:
  - chirality x:  modulus 1 (just position 0)
  - left surface: modulus ⌈(n-1)/2⌉ (odd positions)
  - right surface: modulus ⌊(n-1)/2⌋ (even positions)
```

This is the "Cantor spectral gap" — chiral projection halves the dimension.
-/

import Cantor
import Mathlib.Algebra.Ring.Parity

namespace Chirality

open Cantor CantorPred

/-!
## 1. Chiral Projectors

The three components of a Cantor sequence under chiral decomposition.
-/

/-- Extract the chirality bit (position 0) -/
def chirality (a : Cantor) : Bit := a 0

/-- Project onto the left (odd) surface: positions 1, 3, 5, ... -/
def projectLeft (a : Cantor) : Cantor := fun i => a (2 * i + 1)

/-- Project onto the right (even) surface: positions 2, 4, 6, ... -/
def projectRight (a : Cantor) : Cantor := fun i => a (2 * i + 2)

/-- The inverse: combine chirality, left, and right into a full sequence -/
def combine (x : Bit) (l r : Cantor) : Cantor := Fast.branch x l r

/-!
## 2. Branch Position Lemmas

Exact characterization of how `branch` maps positions.
-/

@[simp]
theorem branch_pos_zero (x : Bit) (l r : Cantor) :
    Fast.branch x l r 0 = x := by
  simp [Fast.branch]

@[simp]
theorem branch_pos_odd (x : Bit) (l r : Cantor) (i : Nat) :
    Fast.branch x l r (2 * i + 1) = l i := by
  simp only [Fast.branch]
  have h1 : 2 * i + 1 ≠ 0 := by omega
  have h2 : ¬(2 ∣ 2 * i + 1) := fun ⟨k, hk⟩ => by omega
  simp only [h1, ↓reduceIte, h2]
  congr 1
  omega

@[simp]
theorem branch_pos_even (x : Bit) (l r : Cantor) (i : Nat) :
    Fast.branch x l r (2 * i + 2) = r i := by
  simp only [Fast.branch]
  have h1 : 2 * i + 2 ≠ 0 := by omega
  have h2 : 2 ∣ 2 * i + 2 := ⟨i + 1, by omega⟩
  simp only [h1, ↓reduceIte, h2]
  congr 1
  omega

/-!
## 3. The Chiral Decomposition Theorem

Every Cantor sequence equals its chiral reconstruction.
-/

/-- Helper: classify a natural number as 0, odd, or positive even -/
theorem nat_trichotomy (n : Nat) :
    n = 0 ∨ (∃ k, n = 2 * k + 1) ∨ (∃ k, n = 2 * k + 2) := by
  cases n with
  | zero => left; rfl
  | succ m =>
    rcases Nat.even_or_odd m with ⟨k, heven⟩ | ⟨k, hodd⟩
    · -- m is even: m = 2k, so m+1 = 2k+1 (odd)
      right; left
      exact ⟨k, by omega⟩
    · -- m is odd: m = 2k+1, so m+1 = 2k+2 (positive even)
      right; right
      exact ⟨k, by omega⟩

/-- **Chiral Decomposition**: a = combine(chirality a, projectLeft a, projectRight a) -/
theorem chiral_decomposition (a : Cantor) :
    combine (chirality a) (projectLeft a) (projectRight a) = a := by
  funext n
  rcases nat_trichotomy n with h0 | ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 0: chirality
    simp only [h0, combine, chirality, branch_pos_zero]
  · -- n = 2k+1: odd position, from left surface
    simp only [hk, combine, branch_pos_odd, projectLeft]
  · -- n = 2k+2: even position, from right surface
    simp only [hk, combine, branch_pos_even, projectRight]

/-- Chirality is extracted correctly -/
theorem chirality_of_combine (x : Bit) (l r : Cantor) :
    chirality (combine x l r) = x := by
  simp [chirality, combine]

/-- Left projection is extracted correctly -/
theorem projectLeft_of_combine (x : Bit) (l r : Cantor) :
    projectLeft (combine x l r) = l := by
  funext i
  simp [projectLeft, combine]

/-- Right projection is extracted correctly -/
theorem projectRight_of_combine (x : Bit) (l r : Cantor) :
    projectRight (combine x l r) = r := by
  funext i
  simp [projectRight, combine]

/-!
## 4. Grade Descent Bounds

Precise bounds on how much the grade decreases via chiral decomposition.
-/

/-- Left surface modulus bound -/
def leftModulus (n : Nat) : Nat := n / 2

/-- Right surface modulus bound -/
def rightModulus (n : Nat) : Nat := (n - 1) / 2

/-- Left modulus is strictly less than n for n ≥ 2 -/
theorem leftModulus_lt (n : Nat) (hn : n ≥ 2) : leftModulus n < n := by
  unfold leftModulus
  omega

/-- Right modulus is strictly less than n for n ≥ 2 -/
theorem rightModulus_lt (n : Nat) (hn : n ≥ 2) : rightModulus n < n := by
  unfold rightModulus
  omega

/-- Both surface moduli are strictly less than n for n ≥ 2 -/
theorem surface_moduli_lt (n : Nat) (hn : n ≥ 2) :
    leftModulus n < n ∧ rightModulus n < n :=
  ⟨leftModulus_lt n hn, rightModulus_lt n hn⟩

/-- Left modulus for n ≥ 1 -/
theorem leftModulus_lt_of_pos (n : Nat) (hn : n ≥ 1) : leftModulus n ≤ n := by
  unfold leftModulus
  omega

/-- Right modulus for n ≥ 1 -/
theorem rightModulus_lt_of_pos (n : Nat) (hn : n ≥ 1) : rightModulus n < n := by
  unfold rightModulus
  omega

/-!
## 5. Modulus Reduction via Chiral Decomposition

The key insight: composing a predicate with `branch` reduces the effective modulus.
-/

/-- If two sequences agree on first n bits, their projections agree on ~n/2 bits -/
theorem projectRight_eq_of_eq {a b : Cantor} {n : Nat}
    (hab : ∀ i < n, a i = b i) :
    ∀ i < (n - 1) / 2, projectRight a i = projectRight b i := by
  intro i hi
  simp only [projectRight]
  apply hab
  -- Need: 2*i + 2 < n, given: i < (n-1)/2
  -- From i < (n-1)/2, we get 2*i < n-1, so 2*i + 2 < n + 1
  -- More precisely: 2*i + 1 < n - 1, so 2*i + 2 < n
  have h1 : i * 2 < ((n - 1) / 2) * 2 := by omega
  have h2 : ((n - 1) / 2) * 2 ≤ n - 1 := Nat.div_mul_le_self (n - 1) 2
  omega

/-- If two sequences agree on first n bits, their projections agree on ~n/2 bits -/
theorem projectLeft_eq_of_eq {a b : Cantor} {n : Nat}
    (hab : ∀ i < n, a i = b i) :
    ∀ i < n / 2, projectLeft a i = projectLeft b i := by
  intro i hi
  simp only [projectLeft]
  apply hab
  -- Need: 2*i + 1 < n, given: i < n/2
  have h1 : i * 2 < (n / 2) * 2 := by omega
  have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
  omega

/-- The chirality agrees if first bits agree -/
theorem chirality_eq_of_eq {a b : Cantor} {n : Nat} (hn : n ≥ 1)
    (hab : ∀ i < n, a i = b i) :
    chirality a = chirality b := by
  simp only [chirality]
  apply hab
  omega

/-!
## 6. The Right Predicate Modulus Bound

If p has modulus n, composing with combine on the right surface has modulus n/2.
-/

/-- The right predicate after fixing chirality and left -/
def rightPred (p : Cantor → Bool) (x : Bit) (l : Cantor) : Cantor → Bool :=
  fun r => p (combine x l r)

/-- Helper for division bound -/
theorem div2_bound {k n : Nat} (h : 2 * k + 2 < n) : k < n / 2 := by
  have h1 : (k + 1) * 2 ≤ n := by omega
  have h2 : k + 1 ≤ n / 2 := Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.mpr h1
  omega

/-- rightPred has reduced modulus -/
theorem rightPred_hasModulus {p : Cantor → Bool} {n : Nat}
    (hp : ∀ a b : Cantor, (∀ i < n, a i = b i) → p a = p b)
    (x : Bit) (l : Cantor) :
    ∀ r₁ r₂ : Cantor, (∀ i < n / 2, r₁ i = r₂ i) →
      rightPred p x l r₁ = rightPred p x l r₂ := by
  intro r₁ r₂ hr
  unfold rightPred
  apply hp
  intro i hi
  simp only [combine]
  rcases nat_trichotomy i with h0 | ⟨k, hk⟩ | ⟨k, hk⟩
  · simp [h0, Fast.branch]
  · simp only [hk, branch_pos_odd]
  · simp only [hk, branch_pos_even]
    apply hr
    exact div2_bound (hk ▸ hi)

/-!
## 7. Summary: The Grade-Halving Structure

The chiral decomposition creates a tree:

```
        p (modulus n)
            │
    ┌───────┴───────┐
    │               │
  find x          after x fixed
 (2 choices)           │
                ┌──────┴──────┐
                │             │
           find l          find r
       (modulus ~n/2)   (modulus ~n/2)
```

Key equations:
- leftModulus n = n / 2
- rightModulus n = (n - 1) / 2
- Both < n for n ≥ 2

This is the "Cantor spectral gap" — chiral projection halves the dimension,
enabling O(log n) depth instead of O(n).
-/

/-!
## 8. Connection to Fast.find Termination

The termination argument for Fast.find:

1. p has modulus n
2. After fixing chirality x, the left predicate has modulus ≤ leftModulus n
3. After fixing x and l, the right predicate has modulus ≤ rightModulus n
4. For n ≥ 2, both are strictly less than n
5. Base cases: n = 0 (constant predicate), n = 1 (depends only on chirality)
6. Therefore: recursion terminates with depth O(log n)
-/

/-- The termination measure for Fast.find would be the modulus -/
noncomputable def terminationMeasure (p : CantorPred) : Nat := p.modulus

/-!
Note: The actual termination and correctness proofs are in FastFindTotal.lean,
which defines a total version of find with `termination_by p.bound` and proves
`find_correct : ∃ a, p.pred a → p.pred (find p)`.
-/

end Chirality
