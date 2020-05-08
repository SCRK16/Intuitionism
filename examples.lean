import ..Intuitionism.reckless

example (P Q : Prop) : (P ∨ Q) → ¬(¬P ∧ ¬Q) :=
begin
    intros h₁ h₂,
    cases h₁ with hp hq,
    {
        exact h₂.elim_left hp,
    },
    {
        exact h₂.elim_right hq,
    }
end

lemma LEM_equiv_double_not : (∀ P : Prop, P ∨ ¬P) ↔ ∀ Q : Prop, ¬¬Q → Q :=
begin
    split,
    {
        intros h Q nnq,
        cases h Q with hq nq,
        {
            exact hq,
        },
        {
            exfalso,
            exact nnq nq,
        }
    },
    {
        intros h P,
        apply h (P ∨ ¬P),
        exact reckless.not_not_or P,
    }
end

example (P Q : Prop) (lem : ∀ P : Prop, P ∨ ¬P) : ¬(¬P ∧ ¬Q) → P ∨ Q :=
begin
    intro h,
    cases lem P with hp np,
    {-- case: P
        left,
        exact hp,
    },
    {-- case: ¬P
        right,
        have nn := LEM_equiv_double_not.mp lem,
        apply nn Q,
        intro nq,
        exact h (and.intro np nq),
    }
end

-- For the proof that the contrapositive of this is reckless, see reckless.lean
example (P Q : Prop) : (¬P ∨ Q) → (P → Q) :=
begin
    intros h hp,
    cases h with np hq,
    {-- case: ¬P
        exfalso,
        exact np hp,
    },
    {-- case: Q
        exact hq,
    }
end

example (α : Type) (P : α → Prop) : (¬∃ x, P x) → ∀ x, ¬P x :=
begin
    intros h x hpx,
    apply h,
    use x,
    exact hpx,
end