/-
This file defines natural sequences, here defined as functions ℕ → ℕ
Also defined here are the comparisons =, ≠, <, ≤ and #
-/

import data.nat.basic

def nat_seq := ℕ → ℕ

notation `𝒩` := nat_seq

namespace nat_seq

def zero : 𝒩 := λ n, 0

def eq (a b : 𝒩) : Prop := ∀ n : ℕ, a n = b n

infix `='`:50 := eq

def ne (a b : 𝒩) : Prop := ¬ a =' b

infix `≠'`:50 := ne

def lt (a b : 𝒩) : Prop := ∃ n : ℕ, (∀ i : ℕ, i < n → a i = b i) ∧ a n < b n

infix `<` := lt

def le (a b : 𝒩) : Prop := ∀ n : ℕ, (∀ i : ℕ, i < n → a i = b i) → a n ≤ b n 

infix `≤` := le

theorem le_of_eq (a b : 𝒩) (h : a =' b) : a ≤ b :=
begin
    intro n,
    intro hn,
    rw h,
end

lemma imp_eq_iff_imp_eq (a b : 𝒩) (n: ℕ) : 
    (∀ i : ℕ, i < n → a i = b i) ↔ (∀ i : ℕ, i < n → b i = a i) :=
begin
    split,
    repeat {intro h, intro i, intro hi, symmetry, exact h i hi},
end

lemma imp_eq_trans (a b c : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, i < n → a i = b i)
    (h₂ : ∀ i : ℕ, i < n → b i = c i) :
    ∀ i : ℕ, i < n → a i = c i :=
begin
    intro i,
    intro hi,
    have aibi := h₁ i hi,
    rw aibi,
    exact h₂ i hi,
end

@[trans] theorem eq_trans (a b c : 𝒩) : a =' b → b =' c → a =' c :=
begin
    intro ab,
    intro bc,
    intro n,
    rw ab n,
    exact bc n,
end

@[symm] theorem eq_symm (a b: 𝒩) : a =' b ↔ b =' a :=
begin
    split,
    repeat {intros h n, symmetry, exact h n},
end

@[refl] theorem eq_refl (a : 𝒩) : a =' a :=
begin
    intro n,
    refl,
end

@[symm] theorem ne_symm (a b : 𝒩) : a ≠' b ↔ b ≠' a :=
begin
    repeat {rw ne},
    rw eq_symm,
end

lemma lt_eq_lt_le (a b : 𝒩) (n m : ℕ)
        (h1 : ∀ i : ℕ, i < n → a i = b i) (h2 : a m < b m) : 
        n ≤ m :=
begin
    cases le_or_gt n m with nlem ngtm,
    {-- case: n ≤ m
        exact nlem,
    },
    {-- case: m < n
        exfalso,
        rw gt_iff_lt at ngtm,
        have aibi := h1 m ngtm,
        rw eq_iff_le_not_lt at aibi,
        exact (and.elim_right aibi) h2,
    }
end

lemma lt_eq_ne_le (a b : 𝒩) (n m : ℕ)
        (h1 : ∀ i : ℕ, i < n → a i = b i) (h2 : a m ≠ b m) :
        n ≤ m :=
begin
    rw ne_iff_lt_or_gt at h2,
    cases h2 with hlt hgt,
    {-- case: a m < b m
        exact lt_eq_lt_le a b n m h1 hlt,
    },
    {
        rw gt_iff_lt at hgt,
        rw imp_eq_iff_imp_eq at h1,
        exact lt_eq_lt_le b a n m h1 hgt,
    }
end

theorem le_of_lt (a b : 𝒩) (less: a < b) : a ≤ b :=
begin
    rw le,
    rw lt at less,
    intro n,
    intro h,
    cases less with d hd,
    cases hd with p q,
    have hnd := lt_eq_lt_le a b n d h q,
    rw le_iff_eq_or_lt at hnd,
    cases hnd with ndeq ndlt,
    { --case n = d
        rw ← ndeq at q,
        exact nat.le_of_lt q,
    },
    { --case n < d
        apply nat.le_of_eq,
        apply p,
        exact ndlt,
    }
end

@[trans] theorem lt_trans (a b c : 𝒩) : a < b → b < c → a < c :=
begin
    intro hab,
    intro hbc,
    cases hab with n hn,
    cases hbc with m hm,
    cases hn with p₁ p₂,
    cases hm with q₁ q₂,
    use min n m,
    split,
    {--need to prove: ∀ (i : ℕ), i < min n m → a i = c i
        intro i,
        intro hi,
        rw lt_min_iff at hi,
        cases hi with i₁ i₂,
        rw p₁ i i₁,
        exact q₁ i i₂,
    },
    {--need to prove: a (min n m) < c (min n m)
        cases lt_trichotomy n m with nltm h,
        {-- n < m
            have mineqn := min_eq_left (nat.le_of_lt nltm),
            rw mineqn,
            rw ← q₁ n nltm,
            exact p₂,
        },
        {
            cases h with neqm mltn,
            {-- n = m
                rw neqm at *,
                rw min_self,
                exact lt_trans p₂ q₂,
            },
            {-- m < n
                have mineqm := min_eq_right (nat.le_of_lt mltn),
                rw mineqm,
                rw p₁ m mltn,
                exact q₂,
            }
        }
    }
end

-- Doing a finite amount of comparisons is allowed
lemma all_eq_or_exists_neq (a b : 𝒩) (n : ℕ): 
    (∀ i : ℕ, i < n → a i = b i) ∨ (∃ i : ℕ, i < n ∧ (∀ j : ℕ, j < i → a j = b j) ∧ a i ≠ b i) :=
begin
    induction n with d hd,
    {-- case: n = 0
        left,
        intro i,
        intro hi,
        exfalso,
        rw ← not_le at hi,
        exact hi (zero_le i),
    },
    {-- case: succ(n)
        cases hd with all_eq exists_neq,
        {-- hypothesis: ∀ i < d, a i = b i
            have tri := lt_trichotomy (a d) (b d),
            rw or_comm at tri,
            rw or_assoc at tri,
            cases tri with aeqb anb,
            {-- case: a d = b d
                left,
                intro i,
                intro hi,
                rw nat.lt_succ_iff_lt_or_eq at hi,
                cases hi with iltd ieqd,
                exact all_eq i iltd,
                rw ieqd,
                exact aeqb,
            },
            {-- case: a d ≠ b d
                right,
                use d,
                split,
                exact nat.lt_succ_self d,
                split,
                exact all_eq,
                rwa [ne_iff_lt_or_gt, or.comm, gt_iff_lt],
            }
        },
        {-- hypothesis: ∃ i < d, (∀ j < i, a j = b j) ∧ a i ≠ b i
            right,
            cases exists_neq with i hi,
            use i,
            split,
            exact nat.lt_succ_of_lt (and.elim_left hi),
            exact and.elim_right hi,
        }
    }
end


lemma nat_lt_cotrans (a b : ℕ) (h : a < b) : ∀ c : ℕ, a < c ∨ c < b :=
begin
    intro c,
    induction c with d hd,
    {-- case: c = d = 0
        right, -- need to prove: 0 < b
        have ha := nat.eq_zero_or_pos a,
        cases ha with hal har,
        rw hal at h, exact h,
        rw gt_iff_lt at har,
        exact nat.lt_trans har h,
    },
    {-- case: c = succ(d)
        cases hd with ad db,
        {-- case: a < d
            left,
            exact nat.lt_trans ad (nat.lt_succ_self d),
        },
        {-- case d < b
            cases db with i hi,
            {-- b = nat.succ d
                left,
                exact h,
            },
            {-- b > nat.succ d
                right,
                rw nat.lt_succ_iff_lt_or_eq,
                rw or.comm,
                rw ← le_iff_eq_or_lt,
                exact hi,
            }
        }
    }
end

theorem lt_cotrans (a b : 𝒩) (h : a < b) : ∀ c : 𝒩, a < c ∨ c < b :=
begin
    intro c,
    rw lt at h,
    cases h with n hn,
    cases hn with hnl hnr,
    cases all_eq_or_exists_neq a c n with all_eq exists_neq,
    {-- hypothesis all_eq: ∀ i < n, a i = c i
        have hlt := nat_lt_cotrans (a n) (b n) hnr,
        have ltcn := hlt (c n),
        cases ltcn with ancn cnbn,
        {-- hypothesis ancn: a n < c n
            left, -- need to prove: a < c
            rw lt,
            use n,
            exact and.intro all_eq ancn,
        },
        {-- hypothesis cnbn: c n < b n
            right, -- need to prove: c < b
            rw lt,
            use n,
            split,
            {-- need to prove: ∀ i < n, c i = b i
                rw imp_eq_iff_imp_eq a c n at all_eq,
                exact imp_eq_trans c a b n all_eq hnl,
            },
            {-- need to prove: c n < b n
                exact cnbn,
            }
        }
    },
    {-- hypothesis exists_neq: ∃ i < n, a i ≠ c i
        cases exists_neq with i hi,
        cases hi with hil hi2,
        cases hi2 with him hir,
        rw ne_iff_lt_or_gt at hir,
        cases hir with ailtci aigtci,
        {-- hypothesis ailtci: a i < c i
            left, -- need to prove: a < c
            rw lt,
            use i,
            split,
            exact him,
            exact ailtci,
        },
        {-- hypothesis aigtci: i > c i
            rw gt_iff_lt at aigtci,
            right, -- need to prove: c < b
            rw lt,
            use i,
            split,
            {-- need to prove: ∀ j < i, c j = b j
                intro j,
                intro hj,
                rw ← him j hj,
                have jltn := nat.lt_trans hj hil,
                exact hnl j jltn,
            },
            {-- need to prove: c i < b i
                rw hnl i hil at aigtci,
                exact aigtci,
            }
        }
    }
end

theorem le_iff_not_lt (a b : 𝒩) : a ≤ b ↔ ¬ b < a :=
begin
    split,
    {-- need to prove: a ≤ b → ¬ b < a
        intro h,
        rw le at h,
        rw lt,
        intro ex,
        cases ex with n hn,
        have g := h n,
        cases hn with ind blta,
        rw imp_eq_iff_imp_eq b a n at ind,
        have aleb := g ind,
        rw nat.lt_iff_le_not_le at blta,
        exact and.elim_right blta aleb,
    },
    {
        intro h,
        intro n,
        intro hi,
        cases le_or_gt (a n) (b n) with hle hgt,
        exact hle,
        rw gt_iff_lt at hgt,
        exfalso,
        apply h,
        use n,
        split,
        {-- need to prove: ∀ i < n, b i = a i
            rw imp_eq_iff_imp_eq b a n,
            exact hi,
        }, -- need to prove: b n < a n
        exact hgt,
    }
end

-- The following theorem now easily follows from le_iff_not_lt and lt_cotrans
theorem le_trans (a b c : 𝒩) : a ≤ b → b ≤ c → a ≤ c :=
begin
    intro h₁,
    intro h₂,
    rw le_iff_not_lt at *,
    intro h₃,
    have ltorlt := lt_cotrans c a h₃ b,
    cases ltorlt with cb ba,
    exact h₂ cb,
    exact h₁ ba,
end

theorem eq_stable (a b : 𝒩) : ¬¬ a =' b → a =' b :=
begin
    intro notnot,
    intro n,
    have h := lt_trichotomy (a n) (b n),
    cases h with h₁ r,
    {-- case: a n < b n
        exfalso,
        apply notnot,
        apply not_forall_of_exists_not,
        use n,
        rw ← ne_from_not_eq,
        rw ne_iff_lt_or_gt,
        left,
        exact h₁,
    },
    {
        cases r with h₂ h₃,
        {-- case a n = b n
            exact h₂,
        },
        {-- case b n < a n
            exfalso,
            apply notnot,
            apply not_forall_of_exists_not,
            use n,
            rw ← ne_from_not_eq,
            rw ne_iff_lt_or_gt,
            right,
            exact h₃,
        }
    }
end

theorem le_stable (a b : 𝒩) : ¬¬ a ≤ b → a ≤ b :=
begin
    intro notnot,
    intro n,
    intro hn,
    have h := le_or_gt (a n) (b n),
    cases h with h₁ h₂,
    {-- case: a n ≤ b n
        exact h₁,
    },
    {-- case a n > b n
        exfalso,
        apply notnot,
        apply not_forall_of_exists_not,
        use n,
        intro r,
        rw gt_iff_lt at h₂,
        rw lt_iff_le_not_le at h₂,
        cases h₂ with h₃ h₄,
        exact h₄ (r hn),
    }
end

def apart (a b : 𝒩) : Prop := ∃ n, a n ≠ b n

infix `#` := apart

-- If two natural sequences are apart from eachother, they are not equal
theorem ne_of_apart (a b : 𝒩) (r : a # b) : a ≠' b :=
begin
    intro h,
    cases r with n hn,
    apply hn,
    apply h,
end

theorem eq_iff_not_apart (a b : 𝒩) : a =' b ↔ ¬ a # b :=
begin

    split,
    {-- a = b → ¬ a # b
        intro h,
        intro g,
        cases g with n hn,
        exact hn (h n),
    },
    {-- ¬ a # b → a = b
        intro h,
        intro n,
        rwa [apart, not_exists] at h,
        have g := h n,
        rwa [ne_iff_lt_or_gt, not_or_distrib] at g,
        have tri := lt_trichotomy (a n) (b n),
        cases tri with l r,
        {-- case: a n < b n, can't happen because ¬ a n < b n
            exfalso,
            exact (and.elim_left g) l,
        },
        cases r with rl rr,
        {-- case: a n = b n, trivial
            exact rl,
        },
        {-- case: b n < a n, can't happen because ¬ a n > b n
            exfalso,
            exact (and.elim_right g) rr,
        }
    }
end

theorem apart_iff_lt_or_lt (a b : 𝒩) : a # b ↔ a < b ∨ b < a :=
begin
    split,
    {-- need to prove: a # b → a < b ∨ b < a
        intro ab,
        cases ab with n hn,
        have h := all_eq_or_exists_neq a b n,
        cases h with all_eq exists_neq,
        {-- case: ∀ i < n → a i = b i
            rw ne_iff_lt_or_gt at hn,
            cases hn with ab ba,
            {-- case: a n < b n
                left,
                use n,
                exact and.intro all_eq ab,
            },
            {-- case: a n > b n
                right,
                use n,
                rw gt_iff_lt at ba,
                split,
                rw imp_eq_iff_imp_eq b a n,
                exact all_eq,
                exact ba,
            }
        },
        {-- case: ∃ i < n, (∀ j < i, a j = b j) ∧ a i ≠ b i
            cases exists_neq with i hi,
            cases hi with iltn r,
            cases r with ajbj aineqbi,
            rw ne_iff_lt_or_gt at aineqbi,
            cases aineqbi with aibi biai,
            {-- case: a i < b i
                left,
                use i,
                exact and.intro ajbj aibi,
            },
            {-- case: b i < a i
                right,
                use i,
                split,
                rw imp_eq_iff_imp_eq b a i,
                exact ajbj,
                rw gt_iff_lt at biai,
                exact biai,
            }
        }
    },
    {-- need to prove: a < b ∨ b < a → a # b
        intro aborba,
        cases aborba with ab ba,
        {-- case: a < b
            cases ab with n hn,
            use n,
            rw ne_iff_lt_or_gt,
            left,
            exact and.elim_right hn,
        },
        {-- case: b < a
            cases ba with n hn,
            use n,
            rw ne_iff_lt_or_gt,
            right,
            exact and.elim_right hn,
        }
    }
end

-- The following theorem now easily follows from combining lt_cotrans and apart_iff_lt_or_lt
theorem apart_cotrans (a b : 𝒩) (h : a # b) : ∀ c : 𝒩, a # c ∨ c # b :=
begin
    intro c,
    repeat {rw apart_iff_lt_or_lt at *},
    cases h with ab ba,
    {-- case: a < b
        cases lt_cotrans a b ab c with ac cb,
        {-- case: a < c
            left,
            left,
            exact ac,
        },
        {-- case: c < b
            right,
            left,
            exact cb,
        }
    },
    {-- case: b < a
        cases lt_cotrans b a ba c with bc ca,
        {-- case: b < c
            right,
            right,
            exact bc,
        },
        {-- case: c < a
            left,
            right,
            exact ca,
        }
    }
end

-- 0 is the smallest sequence
lemma zero_le (a : 𝒩) : zero ≤ a :=
begin
    intros n h,
    rw zero,
    simp,
end

lemma apart_zero_lt (a : 𝒩) (h : a # zero) : zero < a :=
begin
    rw apart_iff_lt_or_lt at h,
    cases h with alt agt,
    {-- case: a < 0, impossible
        exfalso,
        have h₁ := zero_le a,
        rw le_iff_not_lt at h₁,
        exact h₁ alt,
    },
    {-- case: 0 < a, trivial
        exact agt,
    }
end

/-
There are uncountably (defined positively) many natural sequences.
The proof of this theorem is Cantor's Diagonal argument
-/
theorem uncountable (f : ℕ → 𝒩): ∃ a : 𝒩, ∀ n : ℕ, a # (f n) :=
begin
    use λ n : ℕ, (f n n) + 1,
    intro n,
    use n,
    exact nat.succ_ne_self (f n n),
end

end nat_seq