open Classical


variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
fun h =>
  Or.elim (em q)
    (fun hq : q =>
      Or.inl (fun _ => hq))
    (fun hnq : ¬q =>
      Or.inr (fun hp : p =>
        match h hp with
        | Or.inl hq => absurd hq hnq
        | Or.inr hr => hr))


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
fun h =>
    Or.elim (em p)
    (
      fun hp : p =>
      Or.elim (em q)
      (
        fun hq: q => absurd (And.intro hp hq)  h
      )
      (
        fun hnq: ¬q => Or.inr hnq
      )

    )
    (
     fun  hnp : ¬p => Or.inl hnp
    )

example : ¬(p → q) → p ∧ ¬q :=
fun h =>
  Or.elim (em p)
    (fun hp =>
      have hnq : ¬q := fun hq => h (fun _ => hq)
      And.intro hp hnq)
    (fun hnp =>

      have h_p_imp_q := fun hp => absurd hp hnp
      absurd h_p_imp_q h)

example : (p → q) → (¬p ∨ q) :=
fun h => Or.elim (em p)
(fun hp => Or.inr (h hp))
(fun hnp => Or.inl hnp)


example : (¬q → ¬p) → (p → q) :=
fun h =>
  fun hp : p =>
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q =>
        absurd hp (h hnq))

example : p ∨ ¬p :=
Or.elim (em p)
(fun hp => Or.inl hp)
(fun hnp => Or.inr hnp )


example : (((p → q) → p) → p) :=
fun h =>
Or.elim (em p)
(fun hp => hp)
(fun hnp =>
  let hpq := fun hp => absurd hp hnp
  absurd (h hpq) hnp
)
