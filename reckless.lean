/-
This file captures the notion of a statement being reckless  
Meaning: A statement that cannot be proven, and whose negation also cannot be proven  

The most important example of recklessness is the law of exluded middle: ∀ P : Prop, P ∨ ¬ P,  
also called "the principle of omniscience"

-/

import ..Intuitionism.nat_seq
import data.nat.basic
import data.nat.parity

variables P Q : Prop

namespace reckless

/--
The principle of omniscience, also called the law of the excluded middle
-/
def PO : Prop := ∀ Q : Prop, Q ∨ ¬Q

def NPO : Prop := ∀ Q : Prop, ¬Q ∨ ¬¬Q

/--
A statement is reckless if it implies the principle of omniscience:  
∀ Q : Prop, Q ∨ ¬ Q
-/
def reckless : Prop → Prop := λ P : Prop, P → PO

def reckless_NPO : Prop → Prop := λ P : Prop, P → NPO

/--
The limited principle of omniscience  
This is the example Brouwer initially used to justify the idea of statements being reckless,  
though it is slightly weaker than PO  
Using the relations = and #, we could also have defined LPO as:  
∀ a : 𝒩, a = nat_seq.zero ∨ a # nat_seq.zero  
Note: for such a it could still be the case that we can prove a ≠ nat_seq.zero  
This is because (∃ n : ℕ, a n ≠ 0) is stronger than (¬ ∀ n : ℕ, a = 0)
-/
def LPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (∃ n : ℕ, a n ≠ 0)

/--
A statement is called reckless_LPO if it implies LPO
-/
def reckless_LPO : Prop → Prop := 
    λ P : Prop, P → LPO

/--
The lesser limited principle of omniscience  
In words, it says that:  
Before knowing when a sequence of natural numbers will stop being 0,  
the person who claims LLPO is true, can already say it will happen at an even index or an odd index  
It's important that the binding of ∨ is outside the binding of ∀ k : ℕ,  
because the statement ∀ k : ℕ, k % 2 = 0 ∨ k % 2 = 1, is always true
-/
def LLPO : Prop := ∀ a : 𝒩, 
    (∀ k : ℕ, (∀ i : ℕ, i < k → a i = 0) ∧ a k ≠ 0 → k % 2 = 0) ∨
    (∀ k : ℕ, (∀ i : ℕ, i < k → a i = 0) ∧ a k ≠ 0 → k % 2 = 1)

def reckless_LLPO : Prop → Prop :=
    λ P : Prop, P → LLPO

-- A simple lemma to show a reckless statement exists: PO itself is reckless
lemma exists_reckless : ∃ P : Prop, reckless P :=
begin
    use PO,
    intro h,
    exact h,
end

-- If a statement implies a reckless statement, it is itself reckless
theorem implies_reckless (h : P → Q) (hq : reckless Q) : reckless P :=
begin
    intro P,
    exact hq (h P),
end

theorem implies_reckless_NPO (h : P → Q) (hq : reckless_NPO Q) : reckless_NPO P :=
begin
    intro P,
    exact hq (h P),
end

-- If a statement implies a reckless_LPO statement, it is itself reckless_LPO
theorem implies_reckless_LPO (h : P → Q) (hq : reckless_LPO Q) : reckless_LPO P :=
begin
    intro P,
    exact hq (h P),
end

-- If a statement implies a reckless_LLPO statement, it is itself LLPO_reckless
theorem implies_reckless_LLPO (h : P → Q) (hq : reckless_LLPO Q) : reckless_LLPO P :=
begin
    intro P,
    exact hq (h P),
end

lemma not_not_of_self : P → ¬¬P :=
begin
    intros h₁ h₂,
    exact h₂ h₁,
end

-- A reckless statement is also reckless_NPO (Or: PO → NPO)
theorem reckless_implies_NPO (h : reckless P) : reckless_NPO P :=
begin
    intro hp,
    intro Q,
    have g := h hp Q,
    cases g with t f,
    {-- case: Q
        right,
        exact (not_not_of_self Q t),
    },
    {-- case: ¬¬Q
        left,
        exact f,
    }
end

-- A reckless statement is also reckless_LPO (Or: PO → LPO)
theorem reckless_implies_LPO (h : reckless P) : reckless_LPO P :=
begin
    intro hp,
    have g := h hp,
    intro a,
    cases g (∃ n : ℕ, a n ≠ 0) with h₁ h₂,
    {-- case: ∃ n : ℕ, a n ≠ 0
        right,
        exact h₁,
    },
    {-- case: ¬∃ n : ℕ, a n ≠ 0
        left,
        have h₃ := forall_not_of_not_exists h₂,
        simp at h₃,
        exact h₃,
    }
end

-- A statement that is reckless_LPO is also reckless_LLPO
theorem LPO_implies_LLPO (h : reckless_LPO P) : reckless_LLPO P :=
begin
    intro hp,
    have g := h hp,
    intro a,
    cases g a with faeq eneq,
    {-- case: ∀ n : ℕ, a n = 0, the conclusion is vacuously true
        left,
        intros k hk,
        exfalso,
        apply and.elim_right hk,
        exact faeq k,
    },
    {-- case: ∃ n : ℕ, a n ≠ 0
        cases eneq with n hn,
        cases nat_seq.all_eq_or_exists_neq a nat_seq.zero n with alleq exneq,
        {-- case: ∀ i < n: a i = 0
            cases nat.mod_two_eq_zero_or_one n with neven nodd,
            {-- case: n is even
                left,
                intros k hk,
                have keqn : k = n, by {
                    have hkn := nat_seq.lt_eq_ne_le a nat_seq.zero k n hk.elim_left hn,
                    have hnk := nat_seq.lt_eq_ne_le a nat_seq.zero n k alleq hk.elim_right,
                    exact le_antisymm hkn hnk,
                },
                rw keqn,
                exact neven,
            },
            {-- case: n is odd
                right,
                intros k hk,
                have keqn : k = n, by {
                    have hkn := nat_seq.lt_eq_ne_le a nat_seq.zero k n hk.elim_left hn,
                    have hnk := nat_seq.lt_eq_ne_le a nat_seq.zero n k alleq hk.elim_right,
                    exact le_antisymm hkn hnk,
                },
                rw keqn,
                exact nodd,
            }
        },
        {-- case: ∃ i < n, (∀ j < i, a j = 0) ∧ a i ≠ 0 
            cases exneq with i hi,
            cases nat.mod_two_eq_zero_or_one i with ieven iodd,
            {-- case: i is even
                left,
                intros k hk,
                have keqi : k = i, by {
                    have hki := nat_seq.lt_eq_ne_le a nat_seq.zero k i hk.elim_left hi.elim_right.elim_right,
                    have hik := nat_seq.lt_eq_ne_le a nat_seq.zero i k hi.elim_right.elim_left hk.elim_right,
                    exact le_antisymm hki hik,
                },
                rw keqi,
                exact ieven,
            },
            {-- case: i is odd
                right,
                intros k hk,
                have keqi : k = i, by {
                    have hki := nat_seq.lt_eq_ne_le a nat_seq.zero k i hk.elim_left hi.elim_right.elim_right,
                    have hik := nat_seq.lt_eq_ne_le a nat_seq.zero i k hi.elim_right.elim_left hk.elim_right,
                    exact le_antisymm hki hik,
                },
                rw keqi,
                exact iodd,
            }
        }
    }
end

/--
Even though PO itself is a reckless statement,
the double negation of PO is still true
-/
lemma not_not_PO : ∀ P : Prop, ¬¬(P ∨ ¬P) :=
begin
    intro P,
    intro h,
    rw not_or_distrib at h,
    apply and.elim_right h,
    exact and.elim_left h,
end

/--
Double negation cannot simply be eliminated for all propositions P
-/
theorem reckless_not_not_implies : reckless (∀ P : Prop, ¬¬P → P) :=
begin
    intro h,
    intro Q,
    have g := h (Q ∨ ¬Q),
    exact g (not_not_PO Q),
end

theorem reckless_implies_not_or : reckless (∀ P Q : Prop, (P → Q) → (Q ∨ ¬P)) :=
begin
    intros h Q,
    apply h Q Q,
    intro hq,
    exact hq,
end

-- Contrapositve
lemma implies_implies_not_implies_not (h : P → Q) : ¬Q → ¬P :=
begin
    intro hq,
    intro hp,
    apply hq,
    exact h hp,
end

/--
Brouwer's first rule of logic
-/
lemma not_not_not_implies_not : ¬¬¬P → ¬P :=
begin
    exact implies_implies_not_implies_not _ _ (not_not_of_self _),
end

theorem reckless_NPO_not_not_or : reckless_NPO (∀ P Q : Prop, ¬¬(P ∨ Q) → (¬¬P ∨ ¬¬Q)) :=
begin
    intros h₁ P,
    have h₂ := h₁ P (¬P) (not_not_PO P),
    cases h₂ with nn nnn,
    {-- case: ¬¬P
        right,
        exact nn
    },
    {-- case: ¬¬¬P
        left,
        exact (not_not_not_implies_not P nnn),
    }
end

/--
If P ∨ ¬P holds for some proposition P, then eliminating double negation is allowed for P
-/
lemma or_not_implies_not_not_implies (h : P ∨ ¬P) : ¬¬P → P :=
begin
    intro hp,
    cases h with p np,
    exact p,
    exfalso,
    exact hp np,
end

/--
This theorem shows that the converse of the previous lemma is reckless_NPO
-/
theorem reckless_NPO_not_not_implies_implies_or_not :
    reckless_NPO (∀ P : Prop, (¬¬P → P) → P ∨ ¬P) :=
begin
    intros h Q,
    have hq := h (¬Q),
    exact hq (not_not_not_implies_not Q),
end

-- A reminder that brackets are important
example : (∀ P : Prop, ¬¬P → P) → (P ∨ ¬P) :=
begin
    intro h,
    exact h (P ∨ ¬P) (not_not_PO P),
end

/-
Classically this would be equivalent to PO  
Constructively, this version is weaker, and unlike PO, always holds
-/
lemma not_and_not : ¬(P ∧ ¬P) :=
begin
    intro h,
    exact h.elim_right h.elim_left,
end

theorem reckless_NPO_not_and_implies_not_or_not :
    reckless_NPO (∀ P Q : Prop, ¬(P ∧ Q) → (¬P ∨ ¬Q)) :=
begin
    intros h P,
    exact h P (¬P) (not_and_not P),
end

/--
Given a b : 𝒩, we already know that a < b → a ≤ b, and that a = b → a ≤ b  
However, this theorem shows that the opposite is not true  
One might expect a ≤ b → a < b ∨ a = b,  
but this statement is actually implies LPO, and therefore reckless
-/
theorem reckless_LPO_le_implies_lt_or_eq :
    reckless_LPO (∀ a b : 𝒩, a ≤ b → a < b ∨ nat_seq.eq a b) :=
begin
    intros h₁ a,
    have hz := nat_seq.zero_le a,
    have h₂ := h₁ nat_seq.zero a hz,
    cases h₂ with zlt zeq,
    {-- case: 0 < a
        right,
        have h₂ := or.intro_left (a < nat_seq.zero) zlt,
        rw ← nat_seq.apart_iff_lt_or_lt at h₂,
        cases h₂ with n hn,
        use n,
        apply ne.symm,
        exact hn,
    },
    {-- case: 0 = a
        left,
        intro n,
        apply eq.symm,
        exact zeq n,
    }
end

-- Similar to (¬ ∀) → (∃ ¬)
theorem reckless_LPO_ne_implies_apart :
    reckless_LPO (∀ a b: 𝒩, nat_seq.ne a b → a # b) :=
begin
    intros h a,
    have h₁ : ∀ n : ℕ, a n = 0 ∨ a n ≠ 0, by
    {-- need to prove: ∀ n : ℕ, a n = 0 ∨ a n ≠ 0
        intro n,
        have tri := nat.lt_trichotomy (a n) 0,
        rwa [or.comm, or.assoc, ← ne_iff_lt_or_gt] at tri,
        cases tri with aneq anne,
        {-- case: a n = 0
            left,
            exact aneq,
        },
        {-- case: an ≠ 0
            right,
            symmetry,
            exact anne,
        },
    },
    
    sorry,
end

-- It is okay to assume PO when deriving a negative conclusion
theorem PO_implies_not_implies_not : (P ∨ ¬P → ¬Q) → ¬Q :=
begin
    intros h hq,
    have h₁ := implies_implies_not_implies_not _ _ h,
    have h₂ := h₁ (not_not_of_self Q hq),
    apply not_not_PO P,
    exact h₂,
end

-- But not when deriving a positive conclusion
theorem reckless_PO_implies : reckless (∀ P Q : Prop, (P ∨ ¬P → Q) → Q) :=
begin
    intros h P,
    have h₁ := h P (P ∨ ¬P),
    apply h₁,
    simp,
end

end reckless

/-
TODO:
Rewrite all code to use @[refl], @[trans], @[symm], etc.
-/

/-
TODO: Important reckless statements
∀ R : α → Prop, ¬ ∀ x : α, R x → ∃ x : ¬ R x
Perhaps some things with ¬ and ∨
-/