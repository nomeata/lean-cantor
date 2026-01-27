/-
# FastFindTotal.lean
# Total (Provably Terminating) Version of Fast.find

This module provides a provably terminating version of Fast.find using the
chiral grade descent principle discovered via GA translation.

## The Fix

The original Fast.find was marked `partial` because Lean couldn't see termination.
By tracking the modulus explicitly and proving it decreases, we get totality.

## Key Insight

After `branch x l r`:
- Left surface has modulus ≤ n/2
- Right surface has modulus ≤ (n-1)/2
- Both strictly < n for n ≥ 2

This gives us our termination measure.

## Correctness

We use the terminating `forsome` (not `Fast.forsome`) to prove correctness.
The terminating `forsome` has a correctness theorem: `forsome_correct`.
-/

import Cantor
import Chirality

namespace FastFindTotal

open Cantor CantorPred Chirality

/-!
## 1. Bounded Predicate Type

A predicate together with a proven modulus bound.
-/

/-- A predicate with a known upper bound on its modulus -/
structure BoundedPred where
  pred : Cantor → Bool
  bound : Nat
  hasModulus : ∀ a b : Cantor, (∀ i < bound, a i = b i) → pred a = pred b

namespace BoundedPred

/-- Lift a CantorPred to a BoundedPred -/
noncomputable def ofCantorPred (p : CantorPred) : BoundedPred where
  pred := p.pred
  bound := p.modulus
  hasModulus := p.eq_of_modulus

/-- Convert a BoundedPred to a CantorPred (for use with terminating forsome) -/
def toCantorPred (p : BoundedPred) : CantorPred where
  pred := p.pred
  hasModulus := ⟨p.bound, p.hasModulus⟩

/-- A constant predicate has bound 0 -/
def const (b : Bool) : BoundedPred where
  pred := fun _ => b
  bound := 0
  hasModulus := fun _ _ _ => rfl

/-!
## 2. Chiral Decomposition for Bounded Predicates

After fixing chirality x, we get predicates on the left and right surfaces
with strictly smaller bounds.

We use the terminating `forsome` (via CantorPred) for correctness proofs.
-/

/-- Inner predicate for right quantification -/
def innerRightPred (p : BoundedPred) (x : Bit) (l : Cantor) : BoundedPred where
  pred := fun r => p.pred (Fast.branch x l r)
  bound := (p.bound - 1) / 2
  hasModulus := by
    intro a b hab
    apply p.hasModulus
    intro i hi
    simp only [Fast.branch]
    by_cases h0 : i = 0
    · simp [h0]
    · by_cases heven : 2 ∣ i
      · -- Even position > 0: comes from a or b (the r argument)
        simp [h0, heven]
        obtain ⟨k, hk⟩ := heven
        cases k with
        | zero => simp at hk; exact absurd hk h0
        | succ j =>
          have hij : (i - 2) / 2 < (p.bound - 1) / 2 := by
            have : i = 2 * j + 2 := by omega
            have : (i - 2) / 2 = j := by omega
            have : 2 * j + 2 < p.bound := by omega
            omega
          have heq : (i - 2) / 2 = j := by omega
          rw [heq]
          exact hab j (by omega)
      · -- Odd position: comes from l, same for both
        simp [h0, heven]

/-- Predicate on left surface: does there exist r such that p(branch x l r)? -/
def leftPred (p : BoundedPred) (x : Bit) : BoundedPred where
  pred := fun l => forsome (innerRightPred p x l).toCantorPred
  bound := p.bound / 2
  hasModulus := by
    intro a b hab
    -- Both sides check if ∃ r, p.pred (branch x _ r)
    -- If a and b agree on first bound/2 positions, the branches agree on odd positions
    -- Show the inner predicates agree
    have h1 : (innerRightPred p x a).pred = (innerRightPred p x b).pred := by
      funext r
      simp only [innerRightPred]
      apply p.hasModulus
      intro i hi
      simp only [Fast.branch]
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases heven : 2 ∣ i
        · -- Even position > 0: comes from r, same for both
          simp [h0, heven]
        · -- Odd position: comes from a or b
          simp [h0, heven]
          have hk : (i - 1) / 2 < p.bound / 2 := by
            have : i ≤ p.bound - 1 := by omega
            have : (i - 1) / 2 ≤ (p.bound - 2) / 2 := by omega
            omega
          exact hab ((i - 1) / 2) hk
    -- The CantorPreds have the same pred, so forsome gives same result
    have hcp : (innerRightPred p x a).toCantorPred = (innerRightPred p x b).toCantorPred := by
      ext; exact congrFun h1 _
    simp only [hcp]

/-- Predicate on right surface after fixing chirality and left (same as innerRightPred) -/
def onRight (p : BoundedPred) (x : Bit) (l : Cantor) : BoundedPred :=
  innerRightPred p x l

/-- Predicate on left surface (same as leftPred) -/
def onLeft (p : BoundedPred) (x : Bit) : BoundedPred :=
  leftPred p x

/-- The existential predicate: does there exist l, r such that p(branch x l r)?
    Uses the terminating forsome for correctness proofs. -/
def existsLR (p : BoundedPred) (x : Bit) : Bool :=
  forsome (leftPred p x).toCantorPred

/-!
## 3. Bound Descent Lemmas

The key to termination: bounds strictly decrease for n ≥ 2.
-/

/-- Left bound is strictly less than original for n ≥ 2 -/
theorem onLeft_bound_lt (p : BoundedPred) (x : Bit) (h : p.bound ≥ 2) :
    (onLeft p x).bound < p.bound := by
  simp only [onLeft, leftPred]
  exact Chirality.leftModulus_lt p.bound h

/-- Right bound is strictly less than original for n ≥ 2 -/
theorem onRight_bound_lt (p : BoundedPred) (x : Bit) (l : Cantor) (h : p.bound ≥ 2) :
    (onRight p x l).bound < p.bound := by
  simp only [onRight, innerRightPred]
  exact Chirality.rightModulus_lt p.bound h

/-!
## 4. The Total Find Function

Now we can define find with explicit termination proof.
-/

/-- Find a witness for a bounded predicate (if one exists) -/
def find (p : BoundedPred) : Cantor :=
  if h : p.bound ≤ 1 then
    -- Base case: predicate depends on at most 1 bit
    -- Just try both values for bit 0 and fill rest with false
    if p.pred (fun _ => false) then fun _ => false
    else if p.pred (fun _ => true) then fun _ => true
    else fun _ => false  -- No witness exists
  else
    -- Recursive case: use chiral decomposition
    have hge2 : p.bound ≥ 2 := by omega
    -- Use Fast.findBit for chirality (only 2 values, always terminates)
    let x := Fast.findBit (fun x => existsLR p x)
    -- Recursively find on left and right surfaces
    let lPred := onLeft p x
    let l := find lPred
    let rPred := onRight p x l
    let r := find rPred
    Fast.branch x l r
termination_by p.bound
decreasing_by
  · -- For left recursion: onLeft reduces bound from n to n/2
    exact onLeft_bound_lt p x hge2
  · -- For right recursion: onRight reduces bound from n to (n-1)/2
    exact onRight_bound_lt p x l hge2

/-!
## 5. Correctness

The find function returns a witness when one exists.
-/

/-- Key lemma: any sequence decomposes as branch of its chirality and projections
    This is equivalent to Chirality.chiral_decomposition -/
theorem cantor_chiral_decomp (a : Cantor) :
    a = Fast.branch (a 0) (fun i => a (2*i+1)) (fun i => a (2*i+2)) := by
  have h := Chirality.chiral_decomposition a
  simp only [Chirality.combine, Chirality.chirality] at h
  exact h.symm

/-- Helper: onRight predicate is satisfied by the right projection of a witness -/
theorem onRight_witness (p : BoundedPred) (x : Bit) (l r : Cantor)
    (h : p.pred (Fast.branch x l r) = true) :
    (onRight p x l).pred r = true := by
  simp only [onRight, innerRightPred]
  exact h

/-- Helper: innerRightPred has a witness when parent has appropriate witness -/
theorem innerRightPred_has_witness (p : BoundedPred) (x : Bit) (l r : Cantor)
    (h : p.pred (Fast.branch x l r) = true) :
    ∃ r', (innerRightPred p x l).pred r' := by
  exact ⟨r, h⟩

/-- Helper: leftPred has a witness when parent has appropriate witness -/
theorem leftPred_has_witness (p : BoundedPred) (x : Bit) (l r : Cantor)
    (h : p.pred (Fast.branch x l r) = true) :
    ∃ l', (leftPred p x).pred l' := by
  use l
  simp only [leftPred]
  rw [forsome_correct]
  exact ⟨r, h⟩

/-- Helper: existsLR is true when a witness with that chirality exists -/
theorem existsLR_of_witness (p : BoundedPred) (x : Bit) (l r : Cantor)
    (h : p.pred (Fast.branch x l r) = true) :
    existsLR p x = true := by
  simp only [existsLR]
  rw [forsome_correct]
  exact leftPred_has_witness p x l r h

/-- Helper: Fast.findBit finds a satisfying bit if one exists -/
theorem findBit_correct (f : Bit → Bool) (h : ∃ b, f b = true) :
    f (Fast.findBit f) = true := by
  simp only [Fast.findBit]
  split_ifs with hf
  · exact hf
  · obtain ⟨b, hb⟩ := h
    cases b
    · exact absurd hb hf
    · exact hb

/-- Helper: correctness for bounded predicates, by strong induction on bound -/
theorem find_correct_aux (n : Nat) (p : BoundedPred) (hn : p.bound = n)
    (h : ∃ a, p.pred a) : p.pred (find p) := by
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    subst hn
    -- Case analysis on bound
    by_cases hbound : p.bound ≤ 1
    · -- Base case: bound ≤ 1
      simp only [find, hbound, ↓reduceDIte]
      by_cases hf : p.pred (fun _ => false) = true
      · simp [hf]
      · by_cases ht : p.pred (fun _ => true) = true
        · simp [hf, ht]
        · -- Neither constant works, but witness exists
          simp [hf, ht]
          -- Show witness exists implies one of the constants works
          obtain ⟨a, ha⟩ := h
          by_cases hzero : a 0 = false
          · -- a 0 = false
            have heq : p.pred (fun _ => false) = p.pred a := by
              apply p.hasModulus
              intro i hi
              have hieq : i = 0 := by omega
              subst hieq
              exact hzero.symm
            rw [heq] at hf
            exact absurd ha hf
          · -- a 0 = true
            simp only [Bool.not_eq_false] at hzero
            have heq : p.pred (fun _ => true) = p.pred a := by
              apply p.hasModulus
              intro i hi
              have hieq : i = 0 := by omega
              subst hieq
              exact hzero.symm
            rw [heq] at ht
            exact absurd ha ht
    · -- Recursive case: bound ≥ 2
      have hge2 : p.bound ≥ 2 := by
        simp only [not_le] at hbound
        omega
      -- Rewrite find for this case using the definition directly
      conv => lhs; rw [find]; simp only [hbound, ↓reduceDIte]
      -- Get witness and decompose it
      obtain ⟨a, ha⟩ := h
      -- Decompose a using chiral_decomposition
      have hdecomp := cantor_chiral_decomp a
      rw [hdecomp] at ha
      let aLeft := fun i => a (2*i+1)
      let aRight := fun i => a (2*i+2)
      -- The chirality that works is a 0
      have hexists : existsLR p (a 0) = true := existsLR_of_witness p (a 0) aLeft aRight ha
      -- findBit finds a working chirality
      let x := Fast.findBit (fun x => existsLR p x)
      have hfindbit : existsLR p x = true := by
        have hex : ∃ b, existsLR p b = true := ⟨a 0, hexists⟩
        exact findBit_correct (existsLR p) hex
      -- The left predicate has a witness
      have hleft_exists : ∃ l', (onLeft p x).pred l' := by
        simp only [onLeft, leftPred, existsLR] at hfindbit ⊢
        rw [forsome_correct] at hfindbit
        exact hfindbit
      -- The bound decreases for left
      have hleft_bound : (onLeft p x).bound < p.bound := onLeft_bound_lt p x hge2
      -- By IH, find on left returns a witness
      let l := find (onLeft p x)
      have hleft : (onLeft p x).pred l := ih (onLeft p x).bound hleft_bound (onLeft p x) rfl hleft_exists
      -- Now show the right predicate has a witness
      have hright_exists : ∃ r', (onRight p x l).pred r' := by
        simp only [onLeft, leftPred] at hleft
        rw [forsome_correct] at hleft
        obtain ⟨r', hr'⟩ := hleft
        exact ⟨r', hr'⟩
      -- The bound decreases for right
      have hright_bound : (onRight p x l).bound < p.bound := onRight_bound_lt p x l hge2
      -- By IH, find on right returns a witness
      let r := find (onRight p x l)
      have hright : (onRight p x l).pred r := ih (onRight p x l).bound hright_bound (onRight p x l) rfl hright_exists
      -- The assembled result satisfies p
      simp only [onRight, innerRightPred] at hright
      exact hright

/-- If a witness exists, find returns a witness -/
theorem find_correct (p : BoundedPred) (h : ∃ a, p.pred a) :
    p.pred (find p) :=
  find_correct_aux p.bound p rfl h

end BoundedPred

/-!
## 6. Wrapping the Original Fast.find

We can now provide a total wrapper for Fast.find.
-/

/-- Total version of Fast.find for predicates with known modulus -/
noncomputable def fastFindTotal (p : CantorPred) : Cantor :=
  BoundedPred.find (BoundedPred.ofCantorPred p)

/-
Note: We could prove that fastFindTotal agrees with the standard CantorPred.find
on witnesses, but they may return different witnesses for the same predicate.
The key property is that both return *a* witness when one exists.
-/

end FastFindTotal
