def hello := "world"

variable (p : Prop)
example : p ∧ q ↔ q ∧ p :=
Iff.intro
(
    fun h => And.intro (h.right) (h.left)
)
(
    fun h=> And.intro (h.right) (h.left)
)


example: p ∨ q ↔ q ∨ p :=
Iff.intro
(
    fun h =>  Or.elim h (fun hp =>  Or.inr hp ) (fun hq => Or.inl hq)
)
(
    fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
)

-- Associativity equivalences
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
(
    fun h: (p ∧ q) ∧ r =>  And.intro (h.left.left) (And.intro h.left.right h.right)
)
(
    fun h: p ∧ (q ∧ r)=> And.intro (And.intro h.left h.right.left) h.right.right
)

example (p q r : Prop): (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
Iff.intro
(
    fun h: (p ∨ q) ∨ r => show  p ∨ (q ∨ r)  from
    Or.elim h (fun hpq: p ∨ q =>
        Or.elim hpq (
            fun hp: p=>
            show p ∨ (q ∨ r)  from Or.intro_left  (q ∨ r) hp
        )
        (
            fun hq: q=>
             have hqr : q ∨ r := Or.intro_left r hq
             show p ∨ (q ∨ r)  from Or.intro_right p hqr
        )
    ) (
        fun hr: r =>
        have hqr : q ∨ r := Or.intro_right q hr
        show p ∨ (q ∨ r)  from Or.intro_right p hqr
    )
)

(
fun h:  p ∨ (q ∨ r)   => show (p ∨ q) ∨ r from
    Or.elim h
    (
        fun hp: p =>
        have hqp : p ∨ q := Or.intro_left q hp
        show (p ∨ q) ∨ r from Or.intro_left r hqp
    )
    (fun hpr: q∨ r =>
        Or.elim hpr (
            fun hq: q=>
            have hpq := Or.intro_right p hq
            show (p ∨ q) ∨ r  from Or.intro_left r hpq
        )
        (
            fun hr: r =>

             show (p ∨ q) ∨ r  from Or.intro_right (p ∨ q) hr
        )
    )

)

-- Distribuitivity equivalences

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
(fun h : p ∨  (q ∧ r) =>
      Or.elim h
        (fun hp : p =>
            have opq: p ∨ q := Or.intro_left q hp
            have opr: p ∨ r := Or.intro_left r hp
          show (p ∨ q) ∧ (p ∨  r) from And.intro opq opr)
        (fun hr : q ∧ r  =>
            have opq: p ∨ q := Or.intro_right p hr.left
            have opr: p ∨ r := Or.intro_right p hr.right
          show (p ∨ q) ∧ (p ∨  r) from And.intro opq opr))
(

   (fun h : (p ∨ q) ∧ (p ∨ r) =>
    Or.elim h.left
      (fun hp : p =>
        show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
      (fun hq : q =>
        Or.elim h.right
          (fun hp : p =>
            show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
          (fun hr : r =>
            have hqr : q ∧ r := And.intro hq hr
            show p ∨ (q ∧ r) from Or.intro_right p hqr)
        )
    )
)


example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
  (fun (h : p → q → r) =>
    fun (hpq : p ∧ q) =>
      h hpq.left hpq.right)
  (fun (h : p ∧ q → r) =>
    fun (hp : p) =>
      fun (hq : q) =>
        h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
  (fun (h : (p ∨ q) → r) =>
    And.intro
      (fun (hp : p) => h (Or.inl hp))
      (fun (hq : q) => h (Or.inr hq))
  )

(
 (fun (h : (p → r) ∧ (q → r)) =>
    fun (pq : p ∨ q) =>
      Or.elim pq
        (fun (hp : p) => h.left hp)
        (fun (hq : q) => h.right hq))

)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h => And.intro
      (fun hp => h (Or.inl hp))
      (fun hq => h (Or.inr hq)))
    (fun h hpq =>
      Or.elim hpq
        (fun hp => h.left hp)
        (fun hq => h.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
fun h =>
  fun hpq =>
    Or.elim h (
      fun hnp => hnp hpq.left)
    (
      fun hnq => hnq hpq.right
    )

example : ¬(p ∧ ¬p) :=
  fun h =>  h.right h.left


example : p ∧ ¬q → ¬(p → q) :=
fun h =>
  fun hpq: p → q =>
    have hq := (hpq h.left)
    show False from h.right hq


example : ¬p → (p → q) :=
  fun hnp =>
    fun hp =>
      False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
fun h =>
  fun hp =>
    Or.elim h
    (fun hnp => False.elim (hnp hp))
    (fun hq => hq)

example : p ∨ False ↔ p := Iff.intro
(fun h =>
Or.elim h (
 fun hp => hp)
( (fun hf => False.elim hf)))
(
  fun hp =>
    Or.inl hp
)

example : p ∧ False ↔ False := Iff.intro
(
  fun hpf =>  hpf.right
)
(
  fun hf => False.elim hf
)

example : (p → q) → (¬q → ¬p) :=
fun hptoq =>
  fun hnq =>
    fun hp =>
      hnq (hptoq hp)
