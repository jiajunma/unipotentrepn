import Mathlib

variable (A B : Prop) (H : A = B)

variable (h : A ∧ B)

#check h.1
#check h.2

#check h.1 = h.2

example : B := h.right

example : A := h.left

def andSwap : B ∧ A := ⟨ h.2, h.1 ⟩

#print andSwap

variable (y : Nat)

def f := fun x => x^2 + 1
def g := fun y => y^2 + 1

variable (x y : Nat)

abbrev F := fun z : Nat => z^2 + y

#check F x

-- F x ≠ fun ? => ?^2 +x

example : F x =  fun z => z^2 + x := rfl

example : F x y = y^2 + x := rfl
-- example : F x y = y^2 + y := rfl --WRONG


-- ite c e_1 e_2 ---> return e_1 or e_2 (type of e_1 = type of e_2 = type of the return)

#check ite
#check ite true
#check ite true 10  0
#eval ite false 10 20

def myIte (b : Bool) (t e : α) : α :=
  match b with
  | true => t
  | false => e

#eval myIte true 10 20
#eval myIte false 10 20

abbrev CBool := {α : Type} → α → α → α

def ctrue : CBool := fun {_} t f => t

def cfalse : CBool := fun {_} t f => f

def cIte (b : CBool) (t e : α) : α :=
  b t e

#eval cIte ctrue 10 20
#eval cIte cfalse 10 20


variable (F : A-> B)
variable (G : B -> C)

variable (a : A)
#check G (F a)

#check G ∘ F


#check Vector String


#check Vector String 0 = Vector String 1

example : Vector String (n+1) = Vector String (1+n) := by
  have H : 1+n = n+1 := by omega
  rw! [H]
  rfl

example : Vector String (n+1) = Vector String (1+n) := by
  simp [Nat.add_comm]


def V : Vector Nat 0 := #v[]
def V' : Vector Nat 1 := #v[42]
-- def V : Vector Nat 1 := #v[42,32]


def prime := fun p => (
  p >1 ∧ ∀ a b : ℕ, a>0 -> b>0 -> a*b =p -> (a = p ∨ b = p))

#check prime

abbrev dt := (fun x: Nat => if x=0  then Nat else String)



#check  dt 0


#check A ∨ B

example (a : A) : A ∨ B := Or.inl a

example (b : B) : A ∨ B := Or.inr b


def noneg := Π x: Nat, x ≥ 0

def noneg' := ∀ x : Nat, x≥ 0

example : noneg = noneg' := rfl

def geqfive := ∃ x : Nat, x ≥ 5

-- def geqfive' := Σ x : Nat, (x ≥ 5)



lemma geqfive' : ∃ x : Nat, 5 ≤  x :=
  ⟨5, Nat.le_refl 5⟩

#print geqfive'


example : Nat.succ 0= 1 := rfl

example : Nat.succ 1 = 2 := rfl
example : Nat.succ (Nat.succ 0) = 2 := rfl



example : [1] = List.cons 1 .nil := rfl

example : [1,2] = List.cons 1 [2] := rfl

example : [1,2] = List.cons 1 (List.cons 2 .nil) := rfl

def onetoten := [1,2,3,4,5,6,7,8,9,10]

#print onetoten
