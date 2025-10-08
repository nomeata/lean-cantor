abbrev Bit := Bool

def Cantor : Type := Nat -> Bit

def cantor_cons (x : Bit) (a : Cantor) (i : Nat) : Bit :=
  if i == 0 then x else a (i - 1)

infix:60 " # " => cantor_cons

def cantorTl (a : Cantor) : Cantor := fun i => a (i + 1)

@[simp] theorem tail_cons_eq (a : Cantor) : cantorTl (x # a) = a
    := by
    funext i
    simp [cantorTl, cantor_cons]

@[simp] theorem head_cons_tail_eq (a : Cantor) : a 0 # cantorTl a = a
    := by
    funext i
    simp [cantorTl, cantor_cons]
    grind

def eqUpTo (i : Nat) (a : Cantor) (b : Cantor) : Bool :=
    match i with
    | 0 => True
    | n + 1 => a 0 == b 0 && eqUpTo n (cantorTl a) (cantorTl b)

def eqUpToRev (i : Nat) (a : Cantor) (b : Cantor) : Bool :=
    match i with
    | 0 => True
    | n + 1 => a n == b n && eqUpToRev n a b

def eqUpToAbstract (i : Nat) (a b : Cantor) : Prop := ∀j < i, a j = b j

theorem eqUpTo_eq_eqUpToAbstract (i : Nat) (a b : Cantor)
  : eqUpTo i a b ↔ eqUpToAbstract i a b
  := by
  induction i generalizing a b with
  | zero => simp [eqUpTo, eqUpToAbstract]
  | succ i IH =>
    apply Iff.intro
    · intro h_eqUpTo
      simp [eqUpTo] at h_eqUpTo
      have ⟨h_zero, h_tl⟩ := h_eqUpTo
      clear h_eqUpTo

      have IH' := (IH _ _).mp h_tl
      clear IH
      simp [eqUpToAbstract, cantorTl] at IH'

      simp [eqUpToAbstract]
      intro j h_j_leq_i
      cases h_j_leq_i with
      | refl => cases i with
        | zero => exact h_zero
        | succ i =>
          apply IH'
          simp
      | step h_j_lt_i =>
        cases j with
        | zero => exact h_zero
        | succ j =>
          apply IH'
          simp at h_j_lt_i
          apply Nat.lt_iff_add_one_le.mpr
          omega
    · intro h_eqUpToAbstract
      simp [eqUpTo]
      apply And.intro
      · apply h_eqUpToAbstract
        simp
      · apply (IH _ _).mpr
        -- TODO: theorem-ify?
        simp [eqUpToAbstract, cantorTl]
        simp [eqUpToAbstract] at h_eqUpToAbstract
        intro j h_j_lt_i
        apply h_eqUpToAbstract
        simp [h_j_lt_i]

theorem eqUpToRev_eq_eqUpToAbstract (i : Nat) (a b : Cantor)
  : eqUpToRev i a b ↔ eqUpToAbstract i a b
  := by
  induction i with
  | zero => simp [eqUpToRev, eqUpToAbstract]
  | succ i IH =>
    simp [eqUpToRev, eqUpToAbstract, IH]
    clear IH
    apply Iff.intro
    · intro ⟨h_i_a_eq_b, h_lt_i_a_eq_b⟩ j h_j_le_i
      cases h_j_le_i with
      | refl => exact h_i_a_eq_b
      | step h_succ_j_le_i =>
        simp at h_succ_j_le_i
        apply h_lt_i_a_eq_b
        apply Nat.lt_iff_add_one_le.mpr
        exact h_succ_j_le_i
    · intro h_abstract
      apply And.intro
      · apply h_abstract
        simp
      · intro j h_j_lt_i
        apply h_abstract
        omega

theorem eqUpTo_eq_eqUpToRev (i : Nat) (a b : Cantor)
  : eqUpTo i a b ↔ eqUpToRev i a b
  := by
  simp [eqUpTo_eq_eqUpToAbstract i a b, eqUpToRev_eq_eqUpToAbstract i a b]

theorem eqUpTo_antimonotone (i j : Nat) (h_i_lt_j : i ≤ j) (a b : Cantor)
  : eqUpTo j a b → eqUpTo i a b
  := by
  simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract]
  intro h_eqUpTo_j k h_k_lt_i
  apply h_eqUpTo_j
  omega

/-
theorem eqUpTo_alt_def (i : Nat) (h : i > 0) (a b : Cantor)
  : a 0 = b 0 ∧ eqUpTo (i - 1) (cantorTl a) (cantorTl b) ↔ a (i - 1) == b (i - 1) ∧ eqUpTo (i - 1) a b
  := by
  induction i generalizing a b with
  | zero => simp [eqUpTo]
  | succ i IH =>
    simp
    apply Iff.intro
    intros h_normal_def


theorem eqUpTo_def_iff_eqUpToRev_def (i : Nat) (a b : Cantor)
  : a 0 = b 0 ∧ eqUpTo i (cantorTl a) (cantorTl b) ↔ a i == b i ∧ eqUpToRev i a b
  := by
  induction i generalizing a b with
  | zero => simp [eqUpTo, eqUpToRev]
  | succ i IH =>
    simp [eqUpTo, eqUpToRev]
    apply Iff.intro
    intro ⟨h_zero, h_zero_tl, ⟩


theorem eqUpToRev_helper (i : Nat) (a b : Cantor)
  : a 0 = b 0 ∧ eqUpToRev i (cantorTl a) (cantorTl b) ↔ eqUpToRev (i + 1) a b
  := by
  induction i generalizing a b with
  | zero => simp [eqUpToRev]
  | succ i IH =>
    apply Iff.intro
    · intro h
      have h_IH := (IH _ _).mpr h.right
      simp [eqUpToRev]
      simp [cantorTl] at h_IH
    · sorry

theorem eqUpTo_eq_eqUpToRev (i : Nat) (a b : Cantor)
  : eqUpTo i a b ↔ eqUpToRev i a b
  := by
  induction i generalizing a b with
  | zero => simp [eqUpTo, eqUpToRev]
  | succ i IH =>
    simp [eqUpTo, eqUpToRev]

  /-
    apply Iff.intro
    · intro h_eqUpTo
      simp [eqUpToRev]
      apply And.intro
      · simp [eqUpTo] at h_eqUpTo
        have ⟨h_zero, h_tl⟩ := h_eqUpTo
        clear h_eqUpTo
        have IH := (IH _ _).mp h_tl
        sorry -- eqUpToRev_helper
      · sorry
    · sorry
  -/

theorem eqUpTo_forall (i : Nat) (a : Cantor) (b : Cantor) :
  eqUpTo i a b ↔ (∀ j < i, a i = b i) := by
  induction i with
  | zero => simp [eqUpTo]
  | succ n IH =>
    apply Iff.intro
    · intros h_eqUpTo
      intros j h_j_lt_succ_n
      simp [eqUpTo] at h_eqUpTo

    · sorry
-/

-- Extensional (!) modulus of uniform continuity
def HasModulus (p : Cantor -> Bool) := ∃ n, ∀a b : Cantor, eqUpTo n a b → p a = p b

noncomputable def modulus p (h : HasModulus p) : Nat :=
  -- open Classical in Nat.find h
  sorry

theorem eq_of_modulus (h : HasModulus p) :
    ∀a b : Cantor, eqUpTo (modulus p h) a b → p a = p b := by
  open Classical in
  unfold modulus
  -- exact Nat.find_spec h
  sorry

theorem eq_of_modulus_eq_0 (h : HasModulus p) (hm : modulus p h = 0) :
    ∀ a b, p a = p b := by
  intro a b
  apply eq_of_modulus h
  simp [hm, eqUpTo]

theorem eqUpTo_cons (i : Nat) (x : Bit) (a b : Cantor)
    : eqUpTo i a b → eqUpTo (i + 1) (x # a) (x # b) := by
    intro h
    simp [eqUpTo]
    simp [cantor_cons, h]

theorem has_modulus_cons : HasModulus p → HasModulus (fun a => p (b # a)) := by
    intro h
    cases h with
    | _ n h_n =>
        cases n with
        | zero =>
            simp [eqUpTo] at h_n
            exists 0
            simp
            simp [eqUpTo]
            intros
            apply h_n
        | succ m =>
            exists m
            intro a b h_mab
            apply h_n
            apply eqUpTo_cons
            apply h_mab

theorem succ_module_cons {x}
    (h : HasModulus p)
: modulus (fun a => p (x # a)) (has_modulus_cons h) ≤ modulus p h - 1 := by
  sorry <;>
  open Classical in
  · apply Nat.find_le
    intro a b hab
    simp
    apply eq_of_modulus h
    have := eqUpTo_cons _ x _ _ hab
    cases hh : modulus p h
    · simp [eqUpTo]
    · simp_all

theorem succ_module_cons_le {x}
    (h : HasModulus p)
: modulus (fun a => p (x # a)) (has_modulus_cons h) ≤ modulus p h := by
  apply Nat.le_trans (succ_module_cons h) (Nat.sub_le _ 1)

def hack : a -> b -> a := fun x _ => x

@[wf_preprocess]
theorem hack_eq (p : Cantor -> Bool) (h : HasModulus p) :
    hack p h f = p (if _ : modulus p h = 0 then fun _ => false else f) := by
  open Classical in
  simp [hack]
  split
  next h2 =>
    apply eq_of_modulus h
    simp [h2, eqUpTo]
  next =>
    rfl

-- attribute [wf_preprocess] cantor_cons

def cantor_cons' (x : Bit) (i : Nat) (a : ∀ j, j + 1 = i → Bit)  : Bit :=
  if h : i == 0 then x else a (i - 1) (by grind)

@[wf_preprocess] theorem cantor_cons_congr (b : Bit) (a : Cantor) (i : Nat) :
    (b # a) i = cantor_cons' b i (fun j _ => a j) := rfl

-- set_option trace.Elab.definition.wf true

mutual
  def forsome (p : Cantor -> Bool) (h : HasModulus p) : Bool :=
      hack p h (find p h)
  termination_by (modulus p h, if modulus p h = 0 then 0 else 1, 0)
  decreasing_by grind

  def find (p : Cantor -> Bool) (h : HasModulus p) : Cantor := fun i =>
    have b := forsome (fun a => p (true # a)) (has_modulus_cons h)
    (b # find (fun a => p (b # a)) (has_modulus_cons h)) i
  termination_by i => (modulus p h, if modulus p h = 0 then 1 else 0, i)
  decreasing_by
  · by_cases modulus p h = 0
    next h0 =>
      have : modulus (fun a => p (true # a)) (has_modulus_cons h) = 0 := by
          have := succ_module_cons_le (x := true) h
          grind
      apply Prod.Lex.right'
      · apply succ_module_cons_le
      · apply Prod.Lex.left
        simp [*]
    next hnn =>
      apply Prod.Lex.left
      apply Nat.lt_of_le_of_lt
      · apply succ_module_cons h
      · exact Nat.sub_one_lt hnn
  · by_cases modulus p h = 0
    next h0 =>
      have : modulus (fun a => p (b # a)) (has_modulus_cons h) = 0 := by
          have := succ_module_cons_le (x := b) h
          grind
      apply Prod.Lex.right'
      · apply succ_module_cons_le
      · apply Prod.Lex.right'
        · simp [*, b]
        · omega
    next hnn =>
      apply Prod.Lex.left
      apply Nat.lt_of_le_of_lt
      · apply succ_module_cons h
      · exact Nat.sub_one_lt hnn
end

def fifth_true (a : Cantor) : Bool := a 5

#eval! List.ofFn (fun (i : Fin 10) => find (fifth_true) (by sorry) i)

theorem find_correct (p : Cantor -> Bool) (h : HasModulus p) (h_exists : ∃ a, p a)
    : p (find p h) := by
  by_cases h0 : modulus p h = 0
  · obtain ⟨a, h_a⟩ := h_exists
    rw [← h_a]
    apply eq_of_modulus_eq_0 h h0
  · rw [find.eq_unfold, forsome.eq_unfold, hack.eq_unfold]
    dsimp -zeta
    extract_lets b
    change p (_ # _)
    by_cases htrue : ∃ a, p (true # a)
    next =>
      have := find_correct (fun a => p (true # a)) (has_modulus_cons h) htrue
      grind
    next =>
      have : b = false := by grind
      clear_value b; subst b
      have hfalse : ∃ a, p (false # a) := by
        obtain ⟨a, h_a⟩ := h_exists
        cases h : a 0
        · exists cantorTl a
          grind [head_cons_tail_eq]
        · exfalso
          apply htrue
          exists cantorTl a
          grind [head_cons_tail_eq]
      clear h_exists
      exact find_correct (fun a => p (false # a)) (has_modulus_cons h) hfalse
termination_by modulus p h
decreasing_by
  · have := succ_module_cons (x := true) h
    grind
  · have := succ_module_cons (x := false) h
    grind

theorem forsome_correct (p : Cantor -> Bool) (h : HasModulus p) :
    forsome p h ↔ (∃ a, p a) where
  mp hfind := by
    unfold forsome hack at hfind
    exists find p h
  mpr hex := by
    unfold forsome hack
    exact find_correct p h hex

theorem not_has_modulus (h : HasModulus p) : HasModulus (fun a => not (p a)) := by
  obtain ⟨n, h_n⟩ := h
  exists n
  intros a b h_ab
  simp
  apply h_n
  exact h_ab

def forevery (p : Cantor -> Bool) (h : HasModulus p): Bool :=
  not (forsome (fun a => not (p a)) (not_has_modulus h))

theorem forevery_correct (p : Cantor -> Bool) (h : HasModulus p) (h_forall : ∀ a, p a) :
    forevery p h ↔ (∀ a, p a) := by
  grind [forevery, forsome_correct, not_has_modulus]


-- idea: clean innser_has_modulus up using
theorem app_has_modulus
  (f : Bool -> Bool -> Bool)
  (h1 : HasModulus p1)
  (h2 : HasModulus p2)
  : HasModulus (fun a => f (p1 a) (p2 a)) :=
  sorry


/-
theorem inner_has_modulus (h : HasModulus p)
  : HasModulus (fun b => eqUpTo n a b -> (p a == p b)) := by
  -- Goal: Predicate only looks at a finite prefix of b
  -- * eqUpTo n a b will look at a prefix of length n
  --    So the modulus is less or equal to n
  -- * p a == p b
  --    has modulus equal to (Nat.find h)
  exists (Nat.max (open Classical in Nat.find h) n)
  intros b c h_b_c_eqUpTo_mod
  simp
  have h_b_c_eqUpTo_n : eqUpTo n b c := by sorry
  have eqUpTo_eq_eqUpTo : eqUpTo n a b = eqUpTo n a c := by sorry
  simp [eqUpTo_eq_eqUpTo]
  suffices _ : p b = p c
  · simp [this]
  · simp [HasModulus] at h
    -- b and c are equal up to the modulus of p
    have h_b_c_eqUpTo_mod_p : eqUpTo (open Classical in Nat.find h) b c := by sorry
    let m := open Classical in Nat.find h
    have h_m := open Classical in Nat.find_spec h
    have h_m_minimal := open Classical in @Nat.find_min _ _ h
    apply (h_m b c h_b_c_eqUpTo_mod_p)
-/

section

open Classical

/-
theorem componentwise_has_modulus_imp_bounded_modulus
  {p : Cantor -> Cantor -> Bool}
  (h_b : ∀ a, HasModulus (p a))
  (h_a : ∀ b, HasModulus (fun a => p a b))
  : ∃ n, ∀ a, Nat.find (h_b a) < n := by
  apply (Mathlib.Tactic.Contrapose.mtr _ h_b)
  simp [HasModulus]
  intro h_wrong
  sorry
-/

end

section

-- The nth element of the output sequence depends on only a finite prefix of any
-- input sequence, for all n.
def HasModuli (f : Cantor -> Cantor)
  := ∀ n, HasModulus (fun a => f a n)


open Classical

/-
theorem has_moduli_imp_eqUpTo
  (f : Cantor -> Cantor)
  (h : HasModuli f)
  : ∀ n, ∃ m, ∀ a b, eqUpTo m a b -> eqUpTo n (f a) (f b)
  := by
  intros n
  simp [HasModuli, HasModulus] at h

  -- m := max 0..n of moduli witnessed by h
  let ns  := { n' : Nat | n' <= n }
  let g (n' : ns) := Nat.find (h n')
  have h_ns_nonempty : Nonempty ns := by
    simp [ns]
    exists n
  have h_max := Finite.exists_max g
  clear h_ns_nonempty
  obtain ⟨arg, h_argmax⟩ := h_max
  simp [ns] at h_argmax
  exists (g arg)

  intros a b
  intro h_eqUpTo_m
  simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract]
  intros j h_j_lt_n
  let m' := Nat.find (h j)
  have h_m' := Nat.find_spec (h j) a b
  have h_m' : eqUpTo m' a b = true → f a j = f b j := h_m'
  apply h_m'; clear h_m'; clear h_m'
  have h_m'_le_g_arg : m' ≤ g arg := by
    unfold g
    unfold m'
    apply h_argmax
    apply Nat.le_of_lt
    exact h_j_lt_n
  apply (eqUpTo_antimonotone _ (g arg))
  · exact h_m'_le_g_arg
  · exact h_eqUpTo_m
end

theorem has_moduli_comp_fun_pred
  (f : Cantor -> Cantor)
  (p : Cantor -> Bool)
  (h_f : HasModuli f)
  (h_p : HasModulus p)
  : HasModulus (fun a => p (f a))
  := by
  simp [HasModulus] at h_p
  simp [HasModulus]
  obtain ⟨n, h_n⟩ := h_p
  obtain ⟨m, h_m⟩ := has_moduli_imp_eqUpTo f h_f n
  exists m
  intros a b h_a_eq_b
  apply h_n
  apply h_m
  apply h_a_eq_b

theorem has_moduli_comp_fun_fun
  (f g : Cantor -> Cantor)
  (h_f : HasModuli f)
  (h_g : HasModuli g)
  : HasModuli (fun a => g (f a))
  := by
  unfold HasModuli
  intro n
  apply (has_moduli_comp_fun_pred f (fun a => g a n))
  · apply h_f
  · apply h_g


section Zipping -- This section contains a bunch of failed attempts

def zip (ab : Cantor × Cantor) := fun n => if decide (Even n) then ab.fst (n / 2) else ab.snd ((n - 1) / 2)

def unzip (c : Cantor) := (fun n => c (2 * n), fun n => c (2 * n + 1))

theorem pair_unpair_id (ab : Cantor × Cantor) : unzip (zip ab) = ab := by
  simp [zip, unzip]

theorem unpair_pair_id (c : Cantor) : zip (unzip c) = c := by
  unfold zip
  unfold unzip
  simp
  ext n
  cases h : (decide (Even n)) with
  | false =>
      have h' : ¬Even n := by
        simp at h
        simp [h]
      simp [h']
      cases n with
      | zero =>
          absurd h'
          simp
      | succ n =>
          apply congr_arg
          simp
          apply Nat.two_mul_div_two_of_even
          apply Nat.even_add_one.not_left.mp
          exact h'
  | true =>
      simp at h
      simp [h]
      apply congr_arg
      apply Nat.two_mul_div_two_of_even
      exact h

def zipped (f : Cantor × Cantor -> T) : Cantor -> T := f ∘ unzip

def unzipped (g : Cantor -> T) : Cantor × Cantor -> T := g ∘ zip

-- this can somehow be strengthened
theorem zipped_modulus_imp_componentwise_modulus
  (p : Cantor → Bool)
  (h : HasModulus p)
  : ∀a, HasModulus (fun b => unzipped p (a, b))
  := by
  simp [HasModulus] at h
  obtain ⟨n, h_n⟩ := h
  intros a
  simp [unzipped]
  simp [HasModulus]
  apply Exists.intro
  · intros b b'
    intro h_b_eq_b'
    apply h_n
    simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract]
    intros j h_j_lt_n
    unfold zip
    simp
    cases h_even_j : decide (Even j) with
    | true =>
      simp at h_even_j
      simp [h_even_j]
    | false =>
      have h_odd_j : ¬Even j := by
        exact of_decide_eq_false h_even_j
      simp [h_odd_j]
      simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract] at h_b_eq_b'
      apply h_b_eq_b'
      suffices (j - 1) / 2 < n + 1 by exact this -- instantiate existential
      trans j + 1
      · apply (lt_of_le_of_lt (b := j - 1))
        · exact Nat.div_le_self (j - 1) 2
        · exact Nat.sub_lt_succ j 1
      · exact Nat.add_lt_add_right h_j_lt_n 1

theorem zipped_modulus_imp_componentwise_modulus_of_fun
  (p : Cantor → Bool)
  (f : Cantor → Cantor)
  (h_p : HasModulus p)
  (h_f : HasModuli f)
  : HasModulus (fun b ↦ unzipped p (f b, b))
  := by
  simp [HasModulus] at h_p
  obtain ⟨n, h_p_n⟩ := h_p
  -- intros a
  simp [unzipped]
  simp [HasModulus]
  apply Exists.intro (max ?_ ?_)
  · intros b b'
    intro h_b_eq_b'
    simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract] at h_b_eq_b'
    apply h_p_n
    simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract]
    intros j h_j_lt_n
    unfold zip
    simp
    cases h_even_j : decide (Even j) with
    | true =>
      simp at h_even_j
      simp [h_even_j]
      simp [HasModuli] at h_f
      obtain ⟨m, h_m⟩ := h_f (j / 2)
      apply h_m
      simp [eqUpTo_eq_eqUpToAbstract, eqUpToAbstract]
      intro j' h_j'_lt_m
      apply h_b_eq_b'
      left
      apply h_j'_lt_m -- :(
      sorry
    | false =>
      have h_odd_j : ¬Even j := by
        exact of_decide_eq_false h_even_j
      simp [h_odd_j]
      apply h_b_eq_b'
      right
      suffices (j - 1) / 2 < n + 1 by exact this -- instantiate existential
      trans j + 1
      · apply (lt_of_le_of_lt (b := j - 1))
        · exact Nat.div_le_self (j - 1) 2
        · exact Nat.sub_lt_succ j 1
      · exact Nat.add_lt_add_right h_j_lt_n 1

end Zipping

theorem componentwise_modulus_imp_modulus
  (p : Cantor × Cantor -> Bool)
  (h_a : ∀b, HasModulus (fun a => p (a, b)))
  (h_b : ∀a, HasModulus (fun b => p (a, b)))
  : HasModulus (zipped p)
  := by
  simp [HasModulus, zipped, unzip]
  sorry -- not a theorem?
-/

/-
theorem forevery_has_modulus
  {p : Cantor -> Cantor -> Bool}
  (h_b : ∀ a, HasModulus (p a))
  (h_a : ∀ f : Cantor -> Cantor, HasModuli f -> HasModulus (fun a => p a (f a)))
  : HasModulus (fun a => forevery (p a) (h_b a)) := by
  simp [forevery]
  simp [forsome]
  simp [hack]
  apply h_a
  simp [HasModuli]
  intros n
  simp [HasModulus]
  exists n
  intros a b H_eq_prefix
  sorry -- not a theorem?
  -- induction (fun a ↦ p a (find (fun a_1 ↦ !p a a_1) (not_has_modulus (h_b a)))) using find.induct with

-- The smallest n, s.t. p agrees on any a and b if a and b share a prefix of
-- length n.
-- Idea: p only inspects a prefix of length 1 of its argument.
def calculate_modulus (p : Cantor -> Bool) (h : HasModulus p) : Nat :=
    least (fun n =>
        forevery (fun a =>
            forevery (fun b =>
                eqUpTo n a b -> (p a == p b)) (inner_has_modulus h)) _) _

    -- Maybe this is why it doesn't work?
    /-  https://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/
    --  > Technical remark.
    --  > The notion of modulus of uniform continuity needed for the proof of
    --  > termination of find_i is not literally the same as above, but a slight
    --  > variant (sometimes called the intensional modulus of uniform continuity,
    --  > whereas ours is referred to as the extensional one). But I won't go into
    --  > such mathematical subtleties here. The main idea is that when the modulus
    --  > is 0 the recursion terminates and one of the branches of the definition of
    --  > find_i is followed, and a new recursion is started, to produce the next
    --  > digit of the example. When the modulus of p is n + 1, the modulus of the
    --  > predicate \a -> p(Zero # a) is or smaller, and so recursive calls are
    --  > always made with smaller moduli and hence eventually
    --  > terminate.
    --  > End of remark.
    -/

section Intensional -- Here's an attempt at defining the intensional modulus of uniform continuity.

-- This is a guess. Based on this definition
/-
Definition 4.8.
  1. A deflation on a type σ is an element of type (σ → σ) that
    (a) is below the identity of σ, and
    (b) has finite image modulo contextual equivalence, that is, its image
      has finitely many equivalence classes.
  2. A (rational) SFP structure on a type σ is a rational chain id n of
    idempotent deflations with ⨆ₙ idₙ = id, the identity of σ.
-/
def id_deflation : Nat -> Cantor -> Cantor :=
  fun n => fun a => fun i => if i < n then a i else 0

-- Intensional (?) modulus of uniform continuity
-- https://martinescardo.github.io/papers/escardo-ho-op-journal.pdf
-- ∃δ ∈ N ∀x ∈ Q, f (x) = f (id δ (x))
def HasIntensionalModulus (p : Cantor -> Bool) :=
  ∃ n, ∀ a, p a = p (id_deflation n a)

-- This is not provable I guess.
theorem all_have_intensional_modulus
  (p : Cantor -> Bool) : HasIntensionalModulus p := by
  simp [HasIntensionalModulus]
  sorry

end Intensional

-/
