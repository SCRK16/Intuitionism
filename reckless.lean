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

/--
The limited principle of omniscience  
This is the example Brouwer initially used to justify the idea of statements being reckless,  
though it is slightly weaker than PO  
Using the relations = and #, we could also have defined LPO as:  
∀ a : 𝒩, a = nat_seq.zero ∨ a # nat_seq.zero  
Note: for such a : 𝒩 it could still be the case that we can prove a ≠ nat_seq.zero  
This is because (∃ n : ℕ, a n ≠ 0) is stronger than (¬ ∀ n : ℕ, a = 0)
-/
def LPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (∃ n : ℕ, a n ≠ 0)

def reckless_LPO : Prop → Prop := λ P : Prop, (PO → P) ∧ (P → LPO)

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
    λ P : Prop, (PO → P) ∧ (P → LLPO)

theorem PO_implies_LPO : PO → LPO :=
begin
    intro hpo,
    intro a,
    cases hpo (∃ n : ℕ, a n ≠ 0) with h₁ h₂,
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

-- A simple lemma to show a reckless statement exists: PO itself is reckless
lemma exists_reckless : ∃ P : Prop, reckless_LPO P :=
begin
    use PO,
    split,
    {-- need to prove: PO → PO
        tauto,
    },
    {-- need to prove: PO → LPO
        exact PO_implies_LPO,
    }
end

theorem LPO_implies_LLPO : LPO → LLPO :=
begin
    intro lpo,
    intro a,
    cases lpo a with faeq eneq,
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
the we have that ¬¬(P ∨ ¬P) is true for all propositions P
-/
lemma not_not_or : ∀ P : Prop, ¬¬(P ∨ ¬P) :=
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
theorem reckless_not_not_implies : reckless_LPO (∀ P : Prop, ¬¬P → P) :=
begin
    split,
    {-- need to prove: PO → ∀ P : Prop, ¬¬P → P
        intros po P nnp,
        have pop : P ∨ ¬P := po P,
        cases pop with hp np,
        {-- case: P
            exact hp,
        },
        {-- case: ¬P
            exfalso,
            exact nnp np,
        }
    },
    {-- need to prove: (∀ P : Prop, ¬¬P → P) → LPO, we prove that it even implies PO
        intro h,
        have po : PO, by {
            intro P,
            apply h,
            exact not_not_or P,
        },
        exact PO_implies_LPO po,
    }
end

theorem reckless_implies_not_or : reckless_LPO (∀ P Q : Prop, (P → Q) → (Q ∨ ¬P)) :=
begin
    split,
    {
        intros po P Q h,
        cases po P with hp np,
        {-- case: P
            left,
            exact h hp,
        },
        {-- case: ¬P
            right,
            exact np,
        }
    },
    {-- need to prove: (∀ (P Q : Prop), (P → Q) → Q ∨ ¬P) → LPO, we prove that it even implies PO
        intros h,
        apply PO_implies_LPO,
        intro Q,
        apply h Q Q,
        intro hq,
        exact hq,
    }
end

/--
Given a b : 𝒩, we already know that a < b → a ≤ b, and that a = b → a ≤ b  
However, this theorem shows that the opposite is not true  
One might expect a ≤ b → a < b ∨ a = b,  
but this statement is actually implies LPO, and therefore reckless
-/
theorem reckless_LPO_le_implies_lt_or_eq :
    reckless_LPO (∀ a b : 𝒩, a ≤ b → a < b ∨ a =' b) :=
begin
    split,
    {-- need to prove: PO → (∀ a b : 𝒩, a ≤ b → a < b ∨ a =' b)
        intros po a b hab,
        cases po (a < b) with hl hnl,
        {-- case: a < b
            left,
            exact hl,
        },
        {-- case: ¬(a < b), we prove: a =' b
            right,
            rw ← nat_seq.le_iff_not_lt at hnl,
            exact nat_seq.eq_of_le_le hab hnl,
        }
    },
    {-- need to prove: (∀ a b : 𝒩, a ≤ b → a < b ∨ a =' b) → LPO
        intros h₁ a,
        have h₂ := h₁ nat_seq.zero a (nat_seq.zero_le a),
        cases h₂ with zlt zeq,
        {-- case: 0 < a
            right,
            have h₂ := or.intro_left (a < nat_seq.zero) zlt,
            rw ← nat_seq.apart_iff_lt_or_lt at h₂,
            cases h₂ with n hn,
            use n,
            exact ne.symm hn,
        },
        {-- case: 0 = a
            left,
            intro n,
            exact eq.symm (zeq n),
        }
    },
end

-- The two following theorems look funny together
theorem implies_not_implies_not : ∀ P Q : Prop, (P ∨ ¬P → ¬Q) → ¬Q :=
begin
    intros P Q h hq,
    have h₁ := mt h,
    have h₂ := h₁ (not_not_intro hq),
    exact (not_not_or P) h₂,
end

theorem reckless_LPO_implies_implies : reckless_LPO (∀ P Q : Prop, (P ∨ ¬P → Q) → Q) :=
begin
    split,
    {
        intros po P Q hpq,
        exact hpq (po P),
    },
    {
        intro h,
        apply PO_implies_LPO,
        intro P,
        have hp := h P (P ∨ ¬P),
        apply hp,
        intro pop,
        exact pop,
    }
end

def WLEM : Prop := ∀ P : Prop, ¬P ∨ ¬¬P

def WLPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (¬∀ n : ℕ, a n = 0)

theorem weak_LEM_implies_weak_LPO : WLEM → WLPO :=
begin
    intros wlem a,
    cases wlem (∃ n : ℕ, a n ≠ 0) with nh nnh,
    {-- case: ¬∃ (n : ℕ), a n ≠ 0
        left,
        have h : ∀ n : ℕ, ¬ a n ≠ 0 := forall_not_of_not_exists nh,
        intro n,
        have hn := h n,
        rwa [ne.def, not_not] at hn,
    },
    {-- case: ¬¬∀ (n : ℕ), a n = 0
        right,
        intro h,
        apply nnh,
        intro nex,
        cases nex with n nhn,
        have hn := h n,
        exact nhn hn,
    }
end

theorem weak_LEM_implies_LLPO : WLEM → LLPO := 
begin
    intros wlem b,
    cases wlem (∀ (k : ℕ), (∀ (i : ℕ), i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 0) with nh nnh,
    {-- case: ¬∀ (k : ℕ), (∀ (i : ℕ), i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 0
        right, -- need to prove: ∀ (k : ℕ), (∀ (i : ℕ), i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 1
        intros k hk,
        rw ← nat.mod_two_ne_zero,
        intro h,
        apply nh,
        intros j hj,
        have hjk : j = k := nat_seq.first_zero_eq b j k hj.elim_left hj.elim_right hk.elim_left hk.elim_right,
        rw hjk,
        exact h,
    },
    {-- case: ¬¬∀ (k : ℕ), (∀ (i : ℕ), i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 0
        left, -- need to prove: ∀ (k : ℕ), (∀ (i : ℕ), i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 0
        intros k hk,
        rw ← nat.mod_two_ne_one,
        rw ← nat.mod_two_ne_zero,
        intro h0,
        apply nnh,
        intro h,
        exact h0 (h k hk),
    }
end

theorem reckless_LLPO_not_not_or : reckless_LLPO (∀ P Q : Prop, ¬¬(P ∨ Q) → (¬¬P ∨ ¬¬Q)) :=
begin
    split,
    {-- need to prove: PO → ∀ (P Q : Prop), ¬¬(P ∨ Q) → ¬¬P ∨ ¬¬Q
        intros po P Q h,
        cases po P with hp np,
        {-- case: P
            left,
            intro np,
            exact np hp,
        },
        {-- case: ¬P
            cases po Q with hq nq,
            {-- case: Q
                right,
                intro nq,
                exact nq hq,
            },
            {-- case: ¬Q
                exfalso,
                apply h,
                intro pq,
                cases pq with hp hq,
                {-- case: P
                    exact np hp,
                },
                {-- case: Q
                    exact nq hq,
                }
            }
        }
    },
    {-- need to prove: (∀ (P Q : Prop), ¬¬(P ∨ Q) → ¬¬P ∨ ¬¬Q) → LPO
        intro h₁,
        apply weak_LEM_implies_LLPO,
        intro P,
        have h₂ := h₁ P (¬P) (not_not_or P),
        cases h₂ with nn nnn,
        {-- case: ¬¬P
            right,
            exact nn
        },
        {-- case: ¬¬¬P
            left,
            exact (not_not_not_iff P).mp nnn,
        }
    }
end

/-
Classically this would be equivalent to PO (they have the same truth table)
Constructively, this version is weaker, and unlike PO, always holds
-/
lemma not_and_not : ¬(P ∧ ¬P) :=
begin
    intro h,
    exact h.elim_right h.elim_left,
end

theorem reckless_LLPO_not_and_implies_not_or_not : reckless_LLPO (∀ P Q : Prop, ¬(P ∧ Q) → (¬P ∨ ¬Q)) :=
begin
    split,
    {-- need to prove: PO → ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q
        intros po P Q h,
        cases po P with hp np,
        {-- case: P
            cases po Q with hq nq,
            {-- case: Q
                exfalso,
                exact h (and.intro hp hq),
            },
            {-- case: ¬Q
                right,
                exact nq,
            }
        },
        {-- case: ¬P
            left,
            exact np,
        }
    },
    {-- need to prove: (∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q) → LLPO
        intro h,
        apply weak_LEM_implies_LLPO,
        intro P,
        exact h P (¬P) (not_and_not P),
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

theorem reckless_LLPO_not_not_implies_or : reckless_LLPO (∀ P : Prop, (¬¬P → P) → P ∨ ¬P) :=
begin
    split,
    {-- need to prove: PO → ∀ (P : Prop), (¬¬P → P) → P ∨ ¬P
        intros po P h,
        exact po P,
    },
    {-- need to prove: (∀ (P : Prop), (¬¬P → P) → P ∨ ¬P) → LLPO
        intro h,
        apply weak_LEM_implies_LLPO,
        intro P,
        have hp := h (¬P),
        exact hp (not_not_not_iff P).mp,
    }
end

-- A reminder that brackets are important
example : (∀ P : Prop, ¬¬P → P) → (∀ P : Prop, P ∨ ¬P) :=
begin
    intros h P,
    exact h (P ∨ ¬P) (not_not_or P),
end

end reckless