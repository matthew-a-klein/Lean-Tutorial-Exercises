
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
