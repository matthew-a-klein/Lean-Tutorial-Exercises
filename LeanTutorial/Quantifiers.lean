
open Classical
variable (α : Type) (p q : α → Prop)

-- 1


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h => And.intro
      (fun x => (h x).left) -- given any x, we have p x
      (fun x => (h x).right)) -- given any x we have q x
    (fun h x => And.intro
      (h.left x)
      (h.right x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
fun h: (∀ x, p x → q x) =>
  fun hp: (∀ x, p x) =>
  fun x =>
    (h x) (hp x)


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
fun h: (∀ x, p x) ∨ (∀ x, q x) =>
  fun x =>
    Or.elim h
    (
      fun hp:   ∀ x, p x => Or.inl (hp x))
    (
      fun hq:   ∀ x, q x => Or.inr (hq x))

-- 2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
fun x: α =>
Iff.intro
(fun h =>
h x)
(fun h => fun _ => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (
  fun h =>
    Or.elim (em r)
      (fun hr => Or.inr hr)
      (fun hnr =>
        Or.inl (fun x =>
          Or.elim (h x)
            (fun hp => hp)
            (fun hr => absurd hr hnr)
        )
    )
  )
  (
  fun h =>
    fun x =>
      Or.elim h
      (fun hp => Or.inl (hp x))
      (fun hr =>  Or.inr hr)
  )


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (fun h=>
    fun hr =>
      fun x =>
        ((h x) hr)
  )
  (
    fun h =>
      fun x =>
        fun hr =>
          h hr x
  )

-- 3 the barber paradox

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (Men : Type) (barber : Men)
  (shaves : Men → Men → Prop)
  (h : ∀ x : Men, shaves barber x ↔ ¬ shaves x x) : False :=
let r := h barber
let s := r.mp
let t := r.mpr
match em (shaves barber barber) with
| Or.inl p => (s p) p
| Or.inr np => np (t np)


--4

def even (n : Nat) : Prop := ∃x: Nat, n = 2 * x

def odd(n: Nat): Prop := ∃ x : Nat, n = 2 * x - 1

def prime (n : Nat) : Prop := n >=2 ∧ ¬∃(x y: Nat), x !=1 ∧ y != 1 ∧ n= x * y

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ x: Nat, n = 2^2^x

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop := ∀n: Nat, n > 2 ∧ even n → ∃ x y: Nat, prime x ∧ prime y ∧ x + y = n

def Goldbach's_weak_conjecture : Prop := ∀n: Nat, odd n ∧ n > 5 → ∃ x y z : Nat, prime x ∧ prime y ∧ prime z ∧ n = x + y + z

def Fermat's_last_theorem : Prop := ∀ a b c: Nat, ¬∃ n: Nat, n > 2 ∧ a^n + b^n = c^n
