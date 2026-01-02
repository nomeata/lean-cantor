import Mathlib.Data.Nat.Find

abbrev Bit := Bool

def Cantor : Type := Nat → Bit

def Cantor.head (a : Cantor) : Bit := a 0

def Cantor.tail (a : Cantor) : Cantor := fun i => a (i + 1)

@[simp, grind] def Cantor.cons (x : Bit) (a : Cantor) : Cantor
  | 0 => x
  | i+1 => a i

infix:60 " # " => Cantor.cons

namespace Partial
mutual
  partial def forsome (p : Cantor → Bool) : Bool :=
    p (find p)

  partial def find (p : Cantor → Bool) : Cantor :=
    have b := forsome (fun a => p (true # a))
    (b # find (fun a => p (b # a)))
end

def fifth_false : Cantor → Bool := fun a => not (a 5)

/-- info: [true, true, true, true, true, false, true, true, true, true] -/
#guard_msgs in
#eval List.ofFn (fun (i : Fin 10) => find fifth_false i)

end Partial

-- Extensional (!) modulus of uniform continuity
def HasModulus (p : Cantor → α) := ∃ n, ∀ a b : Cantor, (∀ i < n, a i = b i) → p a = p b

@[ext] structure CantorPred where
  pred : Cantor → Bool
  hasModulus : HasModulus pred

instance : CoeFun CantorPred (fun _ => Cantor → Bool) where
  coe cp := cp.pred

namespace CantorPred

variable (p : CantorPred)

noncomputable def modulus : Nat :=
  open Classical in Nat.find p.hasModulus

theorem eq_of_modulus : ∀a b : Cantor, (∀ i < p.modulus, a i = b i) → p a = p b := by
  open Classical in
  unfold modulus
  exact Nat.find_spec p.hasModulus

theorem eq_of_modulus_eq_0 (hm : p.modulus = 0) : ∀ a b, p a = p b := by
  intro a b
  apply p.eq_of_modulus
  simp [hm]

def comp_cons (b : Bit) : CantorPred where
  pred := fun a => p (b # a)
  hasModulus := by
    obtain ⟨n, h_n⟩ := p.hasModulus
    cases n with
    | zero => exists 0; grind
    | succ m =>
      exists m
      intro a b heq
      simp
      apply h_n
      intro i hi
      cases i
      · rfl
      · grind

@[simp, grind =] theorem comp_cons_pred (x : Bit) (a : Cantor) :
  (p.comp_cons x) a = p (x # a) := rfl

theorem comp_cons_modulus (x : Bit) :
    (p.comp_cons x).modulus ≤ p.modulus - 1 := by
  open Classical in
  apply Nat.find_le
  intro a b hab
  apply p.eq_of_modulus
  cases hh : p.modulus
  · simp
  · intro i hi
    cases i
    · grind
    · grind
grind_pattern comp_cons_modulus => (p.comp_cons x).modulus

@[wf_preprocess]
theorem coe_wf (p : CantorPred) :
    (wfParam p) f = p (if _ : p.modulus = 0 then fun _ => false else f) := by
  split
  next h => apply p.eq_of_modulus_eq_0 h
  next => rfl

end CantorPred

namespace Almost
mutual
  partial def forsome (p : CantorPred) : Bool := p (find p)

  partial def find (p : CantorPred) : Cantor := fun i =>
    have b := forsome (p.comp_cons true)
    (b # find (p.comp_cons b)) i
end
end Almost

def cantor_cons' (x : Bit) (i : Nat) (a : ∀ j, j + 1 = i → Bit) : Bit :=
  match i with
  | 0 => x
  | j + 1 => a j (by grind)

@[wf_preprocess] theorem cantor_cons_congr (b : Bit) (a : Cantor) (i : Nat) :
  (b # a) i = cantor_cons' b i (fun j _ => a j) := by cases i <;> rfl

mutual
  def forsome (p : CantorPred) : Bool := p (find p)
  termination_by (p.modulus, if p.modulus = 0 then 0 else 1, 0)
  decreasing_by grind

  def find (p : CantorPred) : Cantor := fun i =>
    have b := forsome (p.comp_cons true)
    (b # find (p.comp_cons b)) i
  termination_by i => (p.modulus, if p.modulus = 0 then 1 else 0, i)
  decreasing_by all_goals grind
end

def fifth_false : CantorPred where
  pred a := not (a 5)
  hasModulus := by
    exists 6
    intros a b h_eqUpTo_6
    have h_5_lt_6 : 5 < 6 := by omega
    apply congrArg
    apply h_eqUpTo_6 5 h_5_lt_6

/-- info: [true, true, true, true, true, false, true, true, true, true] -/
#guard_msgs in
#eval List.ofFn (fun (i : Fin 10) => find fifth_false i)

@[simp, grind =] theorem tail_cons_eq (a : Cantor) : (x # a).tail = a := by
  funext i; simp [Cantor.tail, Cantor.cons]

@[simp, grind =] theorem head_cons_tail_eq (a : Cantor) : a.head # a.tail = a := by
  funext i; cases i <;> rfl

theorem find_correct (p : CantorPred) (h_exists : ∃ a, p a) : p (find p) := by
  by_cases h0 : p.modulus = 0
  · obtain ⟨a, h_a⟩ := h_exists
    rw [← h_a]
    apply p.eq_of_modulus_eq_0 h0
  · rw [find.eq_unfold, forsome.eq_unfold]
    dsimp -zeta
    extract_lets b
    change p (_ # _)
    by_cases htrue : ∃ a, p (true # a)
    next =>
      have := find_correct (p.comp_cons true) htrue
      grind
    next =>
      have : b = false := by grind
      clear_value b; subst b
      have hfalse : ∃ a, p (false # a) := by
        obtain ⟨a, h_a⟩ := h_exists
        cases h : a.head
        · exists Cantor.tail a
          grind
        · exfalso
          apply htrue
          exists Cantor.tail a
          grind
      clear h_exists
      exact find_correct (p.comp_cons false) hfalse
termination_by p.modulus
decreasing_by all_goals grind

theorem forsome_correct (p : CantorPred) :
    forsome p ↔ (∃ a, p a) where
  mp hfind := by unfold forsome at hfind; exists find p
  mpr hex := by unfold forsome; exact find_correct p hex

def CantorPred.comp_neg (p : CantorPred) : CantorPred where
  pred a := not (p a)
  hasModulus := by
    obtain ⟨n, h_n⟩ := p.hasModulus
    exists n
    intros a b h_ab
    simp
    apply h_n
    exact h_ab

def forevery (p : CantorPred) : Bool :=
  not (forsome p.comp_neg)

theorem forevery_correct (p : CantorPred) :
    forevery p ↔ (∀ a, p a) := by
  simp [forevery, CantorPred.comp_neg]
  grind [forsome_correct]


inductive Comp α where
  | ret (r : α)
  | ask (k : Bit → Comp α)

def Comp.eval : Comp α → Cantor → α
  | ret r, _ => r
  | ask r, p => (r p.head).eval p.tail

instance : CoeFun (Comp α) (fun _ => Cantor → α) where
  coe cp := cp.eval

@[grind] def Comp.height : Comp α → Nat
  | ret _ => 0
  | ask r => max (r true).height (r false).height + 1

theorem Comp.eqUpToHeight (p : Comp α) (a b : Cantor) (h : ∀ i < p.height, a i = b i) : p a = p b := by
  induction p generalizing a b
  case ret => rfl
  case ask r ih =>
    have : a.head = b.head := h 0 (by grind)
    specialize ih b.head a.tail b.tail
    simp [eval, this]
    apply ih
    intro i hi
    apply h
    cases _ : b.head <;> grind

theorem Comp.hasModulus (p : Comp α) : HasModulus p.eval :=
  ⟨p.height, Comp.eqUpToHeight p⟩

def Comp.asCantorPred (p : Comp Bool) : CantorPred where
  pred := p.eval
  hasModulus := p.hasModulus

def compApprox (n : Nat) (f : Cantor → α) : Comp α :=
  match n with
  | 0 => .ret (f (fun _ => true))
  | n+1 => .ask (fun b => compApprox n (fun a => f (b # a)))

theorem compApprox_correct (hmod : ∀ a b, (∀ i < n, a i = b i) → f a = f b) :
    (compApprox n f).eval = f := by
  funext c
  induction n generalizing f c
  case zero =>
    grind [compApprox, Comp.eval]
  case succ n ih =>
    simp [compApprox, Comp.eval]
    rw [ih]
    case hmod =>
      intro a b heq
      apply hmod
      intro i hi
      cases i <;> grind
    grind

noncomputable def Comp.ofCantorPred (p : CantorPred) : Comp Bool :=
  compApprox p.modulus p.pred

theorem Comp.ofCantorPred_asCantorPred (p : CantorPred) :
    (Comp.ofCantorPred p).asCantorPred = p := by
  ext1; exact compApprox_correct p.eq_of_modulus

namespace Fast

def findBit (p : Bit → Bool) : Bit :=
  if p false then false else true

def branch (x : Bit) (l r : Cantor) : Cantor :=
  fun n =>
    if n = 0      then x
    else if 2 ∣ n then r ((n - 2) / 2)
                  else l ((n - 1) / 2)

mutual
  partial def forsome (p : Cantor -> Bool) : Bool :=
    p (find p)

  partial def find (p : Cantor -> Bool) : Cantor :=
    let x := findBit (fun x => forsome (fun l => forsome (fun r => p (branch x l r))))
    let l := find (fun l => forsome (fun r => p (branch x l r)))
    let r := find (fun r => p (branch x l r))
    branch x l r
end
end Fast
