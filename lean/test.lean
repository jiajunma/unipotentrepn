import Mathlib


variable (P Q : Prop)

def proof1 (h : P ∧ Q) : P ∨ Q := by
  have Pholds : P := h.1
  exact Or.inl Pholds

def proof2 (h : P ∧ Q) : P ∨ Q := by
  have Qholds : Q := h.2
  exact Or.inr Qholds

#check proof1
#check proof2

example : proof1 = proof2 := rfl

def sum1 : Nat ⊕ Nat := Sum.inl 1

def sum2 : Nat ⊕ Nat := Sum.inr 1

example : sum2 ≠  sum1 := Sum.inr_ne_inl


def sum3 : Σ x : Nat, Nat := ⟨1,1⟩

def sum4 : Σ x : Nat, Fin x := ⟨4, 3⟩

#eval sum4.1
#eval sum4.2
#check sum4.2



#print sum4
#check sum4


#check {x : Nat // x >5}

def six : {x : Nat // x >5} := ⟨6, by decide⟩
def seven : {x : Nat // x >5} := ⟨7, by decide⟩


example : six ≠ seven := by
  -- 1. Transform the inequality of subtypes into an inequality of Nats
  intro h
  -- 2. Extract the fact that the values must be equal
  have h_val : six.val = seven.val :=  congr_arg Subtype.val h
  -- 3. This leads to 6 = 7, which is a contradiction
  contradiction


def sixge5 : ∃ x : Nat, x >5 := ⟨6, by decide⟩
def sevenge5 : ∃x : Nat, x >5 := ⟨7, by decide⟩

#print sixge5

example : sixge5 = sevenge5 := rfl

def addcomm1  (a b : ℝ) : a + b = b + a :=
  add_comm a b

def addcomm2 (a b : ℝ) : a + b = b + a := by
    exact add_comm a b

def addcomm3 (a b : ℝ) : a + b = b + a := by
  rw [add_comm]


#print addcomm1
#print addcomm2
-- def addcomm2 : ∀ (a b : ℝ), a + b = b + a :=
-- fun a b => add_comm a b
#print addcomm3
-- def addcomm3 : ∀ (a b : ℝ), a + b = b + a :=
-- fun a b => Eq.mpr (id (congrArg (fun _a => _a = b + a) (add_comm a b))) (Eq.refl (b + a))


theorem my_thm2 (h : a > 0) : 2 * a > 0 := by
   exact Nat.succ_mul_pos 1 h



theorem my_thm (h : a > 0) : 2 * a > 0 := by linarith


#print Nat



#print my_thm

theorem my_lt_trans' (a b c : ℕ) (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans; exact h1; exact h2

#check my_lt_trans'
example (h1 : 3 < 5) (h2 : 5 < 9) : 3 < 9 := my_lt_trans' 3 5 9 h1 h2  -- a, b, c inferred

theorem my_lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans; exact h1; exact h2
example (h1 : 3 < 5) (h2 : 5 < 9) : 3 < 9 := my_lt_trans h1 h2  -- a, b, c inferred



#synth AddGroup ℤ

lemma apply1 (pholds : P) (pimpq : P → Q) : Q := by
    apply pimpq
    assumption

#print apply1


example (a b : ℝ) (h₁ : a + b = 10) (h₂ : a - b = 2) : a = 6 := by
  -- h₁ + h₂
  have h₃ : 2 * a = 12 := by sorry
  linarith

-- `have : ... := by <tactics>` for a tactic-proved intermediate
example (a b: ℝ) : a * b * b *a ≥ 0 := by
  have sq_eq : (a * b)^2  = a * b *b *a := by ring
  rw [← sq_eq]
  positivity


 example : ∀ n : ℕ, n + 0 = n := by
   intro n
   rfl

 example : ∀ a b : ℕ, a + b = b+a := by
    intro a b
    exact add_comm a b

 example : ∃ a : ℕ, a > 5 := by
    use 6
    decide

example (h1 : P -> R) (h2 : Q -> R) : P ∨ Q → R := sorry
