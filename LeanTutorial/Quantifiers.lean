
variable (α : Type) (p q : α → Prop)

-- Basic equivalences
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
