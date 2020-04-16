/-
This file defines the constructive real numbers ℛ,
defined by sequences of shrinking and dwindling rational segments
-/

import ..Intuitionism.segment

/--
We say that a sequence of segments is 'shrinking' if each segment is contained within its predecessor
-/
def shrinking (r : ℕ → 𝕊) := ∀ n, r (n + 1) ⊑ r n

/--
We say that a sequence of segments is 'dwindling' if we can make the segments arbitrarily small
-/
def dwindling (r : ℕ → 𝕊) := ∀ q : ℚ, q > 0 → ∃ n : ℕ, (r n).snd - (r n).fst < q

/--
The definition of real sequences ℛ, representing the real numbers
(Called 'real_seq' here to not interfere with the classical real numbers,  
which are already defined in Lean using Cauchy sequences)  
A real sequence is a sequence of rational segments that shrinks and dwindles
-/
def real_seq := {r : ℕ → 𝕊 // shrinking r ∧ dwindling r}

notation `ℛ` := real_seq

namespace real_seq

/--
Used to extract the underlying sequence of rational segments
-/
def seq (r : ℛ) : ℕ → 𝕊 := subtype.val r

-- We can turn a real segment into a sequence of rationals by only taking the first position
def fst (r : ℛ): ℕ → ℚ :=
begin
    intro n,
    exact (r.seq n).fst,
end

-- We can turn a real segment into a sequence of rationals by only taking the second position
def snd (r : ℛ) : ℕ → ℚ :=
begin
    intro n,
    exact (r.seq n).snd,
end

lemma shrinking (r : ℛ) : shrinking r.val := (subtype.property r).elim_left

lemma dwindling (r : ℛ) : dwindling r.val := (subtype.property r).elim_right

theorem contained_of_le (r : ℛ) {n m : ℕ} (h₁ : n ≤ m) : r.seq m ⊑ r.seq n :=
begin
    induction h₁ with d hd,
    {-- need to prove: seq r n ⊑ seq r n
        refl,
    },
    {-- need to prove: seq r (nat.succ d) ⊑ seq r n
        transitivity (seq r d),
        {-- need to prove: seq r (nat.succ d) ⊑ seq r d
            exact r.shrinking d,
        },
        {-- need to prove: seq r d ⊑ seq r n
            exact h₁_ih,
        }
    }
end

def lt (x y : ℛ) : Prop := ∃ n : ℕ, x.seq n < y.seq n

infix `<` := lt

def le (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≤ y.seq n

infix `≤` := le

def apart (x y : ℛ) : Prop := x < y ∨ y < x

infix `#` := apart

def eq (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≈ y.seq n

infix `='`:50 := eq

def ne (x y : ℛ) : Prop := ¬ x =' y

infix `≠'`:50 := ne

@[trans] theorem lt_trans (x y z: ℛ) (h₁ : x < y) (h₂ : y < z) : x < z :=
begin
    cases h₁ with n hn,
    cases h₂ with m hm,
    use max m n,
    transitivity seq y (max m n),
    {-- need to prove: seq x (max m n) < seq y (max m n)
        have h₁ := contained_of_le x (le_max_right m n),
        have h₂ := contained_of_le y (le_max_right m n),
        apply lt_of_le_of_lt h₁.elim_right,
        apply lt_of_lt_of_le hn,
        exact h₂.elim_left,
    },
    {-- need to prove: seq y (max m n) < seq z (max m n)
        rw segment.lt at *,
        have h₁ := contained_of_le y (le_max_left m n),
        have h₂ := contained_of_le z (le_max_left m n),
        apply lt_of_le_of_lt h₁.elim_right,
        apply lt_of_lt_of_le hm,
        exact h₂.elim_left,
    }
end

lemma lt_or_lt_from_sub_lt_sub {a b c d : ℚ} (h : a - b < c - d) : a < c ∨ d < b :=
begin
    have hac := lt_trichotomy a c,
    cases hac with hl hr,
    {-- case: a < c
        left,
        exact hl,
    },
    {-- case: a = c ∨ c < a
        right,
        cases hr with heq hlt,
        {-- case: a = c
            rwa [heq, sub_eq_add_neg, sub_eq_add_neg, add_lt_add_iff_left, neg_lt_neg_iff] at h,
        },
        {-- case: c < a
            rw ← sub_lt_zero,
            transitivity (c-a),
            {-- need to prove: d - b < c - a
                rwa [lt_sub_iff_add_lt',
                    ← add_sub_assoc,
                    sub_lt_iff_lt_add',
                    ← lt_sub_iff_add_lt,
                    add_sub_assoc, add_comm,
                    ← sub_lt_iff_lt_add] at h,
            },
            {-- need to prove: c - a < 0
                rw ← sub_lt_zero at hlt,
                exact hlt,
            }
        }
    }
end

theorem lt_cotrans (x y z : ℛ) (h₁ : x < y) : x < z ∨ z < y :=
begin
    cases h₁ with n hn,
    rwa [segment.lt, ← sub_pos, ← gt_from_lt] at hn,
    have hz := z.dwindling (segment.fst (seq y n) - segment.snd (seq x n)) hn,
    cases hz with m hm,
    have hm₂ := lt_or_lt_from_sub_lt_sub hm,
    cases hm₂ with zlty xltz,
    {-- case: z.snd m < y.fst n
        right,
        use max m n,
        have h₁ := contained_of_le z (le_max_left m n),
        have h₂ := contained_of_le y (le_max_right m n),
        apply lt_of_le_of_lt h₁.elim_right,
        apply lt_of_lt_of_le zlty,
        exact h₂.elim_left,
    },
    {-- case: x.snd n < z.fst m
        left,
        use max m n,
        have h₁ := contained_of_le z (le_max_left m n),
        have h₂ := contained_of_le x (le_max_right m n),
        apply lt_of_le_of_lt h₂.elim_right,
        apply lt_of_lt_of_le xltz,
        exact h₁.elim_left,
    }
end

theorem apart_cotrans (x y z : ℛ) (h : x # y) : x # z ∨ z # y :=
begin
    cases h with h₁ h₂,
    {-- case: x < y
        cases lt_cotrans x y z h₁ with hz hz,
        {-- case: x < z
            left,
            left,
            exact hz,
        },
        {-- case: z < y
            right,
            left,
            exact hz,
        }
    },
    {-- case: case y < x
        cases lt_cotrans y x z h₂ with hz hz,
        {-- case: y < z
            right,
            right,
            exact hz,
        },
        {-- case: z < x
            left,
            right,
            exact hz,
        }
    }
end

theorem le_iff_not_lt (x y : ℛ) : x ≤ y ↔ ¬ y < x :=
begin
    split,
    {-- need to prove: x ≤ y → ¬ y < x
        intros h₁ h₂,
        cases h₂ with n hn,
        have hn₁ := h₁ n,
        rw segment.le_iff_not_lt at hn₁,
        exact hn₁ hn,
    },
    {-- need to prove: ¬ y < x → x ≤ y
        intros h n,
        rw segment.le_iff_not_lt,
        revert n,
        exact forall_not_of_not_exists h,
    }
end

@[trans] theorem le_trans (x y z : ℛ) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
begin
    rw le_iff_not_lt at *,
    intro zltx,
    cases lt_cotrans z x y zltx with hz hz,
    {-- case: z < y
        exact h₂ hz,
    },
    {-- case: y < x
        exact h₁ hz,
    }
end

@[refl] theorem le_refl (x : ℛ) : x ≤ x :=
begin
    intro n,
    refl,
end

theorem eq_iff_not_apart (x y : ℛ) : x =' y ↔ ¬ x # y :=
begin
    split,
    {-- need to prove: x = y → ¬ x # y
        intros h₁ h₂,
        cases h₂ with xlty yltx,
        {-- case: x < y
            cases xlty with n hn,
            have hn₁ := h₁ n,
            rw segment.lt_iff_not_le at hn,
            exact hn hn₁.elim_right,
        },
        {-- case: y < x
            cases yltx with n hn,
            have hn₁ := h₁ n,
            rw segment.lt_iff_not_le at hn,
            exact hn hn₁.elim_left,
        }
    },
    {-- need to prove: ¬ x # y → x = y
        intros h n,
        rw apart at h,
        rw segment.touches,
        rw not_or_distrib at h,
        split,
        {-- need to prove: seq x n ≤ seq y n
            rw segment.le_iff_not_lt,
            have h₁ := forall_not_of_not_exists h.elim_right n,
            exact h₁,
        },
        {-- need to prove: seq y n ≤ seq x n
            rw segment.le_iff_not_lt,
            have h₂ := forall_not_of_not_exists h.elim_left n,
            exact h₂,
        }
    }
end

@[trans] theorem eq_trans (x y z: ℛ) (h₁ : x =' y) (h₂ : y =' z) : x =' z :=
begin
    rw eq_iff_not_apart,
    intro h₃,
    have h₄ := apart_cotrans x z y h₃,
    cases h₄ with xay yaz,
    {-- case: x # y
        rw eq_iff_not_apart at h₁,
        exact h₁ xay,
    },
    {-- case: y # z
        rw eq_iff_not_apart at h₂,
        exact h₂ yaz,
    }
end

@[refl] theorem eq_refl (x : ℛ) : x =' x :=
begin
    intro n,
    refl,
end

theorem le_stable (x y : ℛ) : ¬¬x ≤ y →  x ≤ y :=
begin
    rw le_iff_not_lt,
    exact not_of_not_not_not,
end

theorem eq_stable (x y : ℛ) : ¬¬x =' y → x =' y :=
begin
    rw eq_iff_not_apart,
    exact not_of_not_not_not,
end

/--
The inclusion from ℚ into ℛ
-/
def inclusion_const (q : ℚ) : ℛ :=
    subtype.mk (λ _ , segment.inclusion q)
    begin
        split,
        {-- need to prove: the defined real_seq is shrinking
            intro n,
            refl,
        },
        {-- need to prove: the defined real_seq is dwindling
            intros e he,
            use 0,
            rw gt_iff_lt at he,
            apply lt_of_le_of_lt _ he,
            apply le_of_eq,
            rw sub_eq_zero,
            refl,
        }
    end

@[instance] def has_zero : has_zero ℛ := { zero := inclusion_const 0 }

/--
The definition of + on real sequences
-/
@[reducible] def add (x y : ℛ) : ℛ := subtype.mk (λ n, segment.add (x.seq n) (y.seq n))
    begin
        have hx := subtype.property x,
        have hy := subtype.property y,
        split,
        {-- need to prove: shrinking
            intro n,
            split,
            {
                apply add_le_add,
                    exact (hx.elim_left n).elim_left,
                    exact (hy.elim_left n).elim_left,
            },
            {
                apply add_le_add,
                    exact (hx.elim_left n).elim_right,
                    exact (hy.elim_left n).elim_right,
            }
        },
        {-- need to prove: dwindling
            intros q hq,
            have hq2 : q / 2 > 0, by
            {
                rw gt_iff_lt,
                apply div_pos,
                exact gt_iff_lt.elim_left hq,
                exact zero_lt_two,
            },
            cases hx.elim_right (q / 2) hq2 with xn hxn,
            cases hy.elim_right (q / 2) hq2 with yn hyn,
            use max xn yn,
            simp,
            rw segment.add,
            rw segment.snd,
            simp,
            rw segment.fst,
            simp,
            rw add_sub_comm,
            have hqa : (q / 2) + (q / 2) = q, by
            {
                rw ← mul_two,
                rw div_mul_cancel,
                exact two_ne_zero,
            },
            rw ← hqa,
            apply add_lt_add,
            {-- need to prove: snd (x.seq (max xn yn)) - fst (x.seq (max xn yn)) < q / 2
                have hm : segment.snd (seq x (max xn yn)) - segment.fst (seq x (max xn yn)) ≤ (segment.snd (x.val xn) - segment.fst (x.val xn)), by
                {-- need to prove: snd - fst of x.seq (max xn yn) < snd - fst of x.seq xn
                    apply segment.contained_bounds_le,
                    apply contained_of_le,
                    exact le_max_left xn yn,
                },
                apply lt_of_le_of_lt hm,
                exact hxn,
            },
            {
                have hm : segment.snd (seq y (max xn yn)) - segment.fst (seq y (max xn yn)) ≤ (segment.snd (y.val yn) - segment.fst (y.val yn)), by
                {-- need to prove: snd - fst of x.seq (max xn yn) < snd - fst of x.seq xn
                    apply segment.contained_bounds_le,
                    apply contained_of_le,
                    exact le_max_right xn yn,
                },
                apply lt_of_le_of_lt hm,
                exact hyn,
            }
        }
    end

theorem add_assoc (x y z : ℛ) : add (add x y) z =' add x (add y z) :=
begin
    intro n,
    split,
    {-- need to prove: add (add x y) z ≤ add x (add y z)
        repeat {
            repeat {rw seq, rw add},
            simp,
        },
        rw segment.add_assoc,
        refl,
    },
    {-- need to prove: add x (add y z) ≤ add (add x y) z
        repeat {
            repeat {rw seq, rw add},
            simp,
        },
        rw ← segment.add_assoc,
        refl,
    }
end

theorem add_comm (x y : ℛ) : add x y =' add y x :=
begin
    intro n,
    split,
    repeat {
        rwa [seq, seq, add, add],
        simp,
        rw segment.add_comm,
    },
end

end real_seq


/-
TODO:
1) Define inclusion from rationals intro reals using: ℚ → ℕ → 𝕊 := λ q, λ n, (q - 1 / 2^n, q + 1 / 2^n)
2) Define 0 using λ n, (0, 0)
3) Show that 0 in (2) and the embedding of 0 in (1) are equal

Create other files for:
5) Intermediate Value Theorem and its constructive counterparts
6) Completeness of (ℛ, ≤)
7) Every real function is continuous (Needs Fan Theorem)
-/