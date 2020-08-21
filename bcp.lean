import ..Intuitionism.nat_seq
import ..Intuitionism.reckless
import data.nat.basic

/--
Brouwer's Continuity Principle
If the relation R on 𝒩×ℕ satisfies:
for all infinite sequences α ∈ 𝒩 there is an n ∈ ℕ such that (α R n),
then the relation should be decidable based on an initial part of α
-/
def BCP : Prop := ∀ R : 𝒩 → ℕ → Prop,
    (∀ a : 𝒩, ∃ n : ℕ, R a n) → ∀ a : 𝒩, ∃ m n : ℕ, ∀ b : 𝒩, (∀ i : ℕ, i < m → a i = b i) → R b n

/--
If a sequence of naturals α and a natural number n are given,
we can always create another sequence that starts out the same,
but differs at n
-/
lemma exists_start_eq_ne (a : 𝒩) (n : ℕ) : ∃ b : 𝒩, (∀ i : ℕ, i < n → a i = b i) ∧ a n ≠ b n :=
begin
    set b : 𝒩 := λ i : ℕ, if i < n then a i else a i + 1 with hb,
    use b,
    split,
    {-- need to prove: ∀ i < n, a i = b i
        intros i hi,
        rw hb,
        simp,
        split_ifs,
        refl,
    },
    {-- need to prove: a n ≠ b n
        rw hb,
        simp,
        have h : ¬ n < n, by simp,
        split_ifs,
        intro neq,
        apply nat.succ_ne_self (a n),
        symmetry,
        exact neq,
    }
end

/--
An example to demonstrate the power of BCP
A function f from 𝒩 to ℕ can never be injective
This can be seen as the other side of the coin to nat_seq.uncountable
That theorem showed a function ℕ → 𝒩 can never be surjective, while this one shows
that a function 𝒩 → ℕ can never be injective
-/
theorem strongly_not_injective (f : 𝒩 → ℕ) : BCP → ∀ a : 𝒩, ∃ b : 𝒩, a # b ∧ f a = f b :=
begin
    intros bcp a,
    set R : 𝒩 → ℕ → Prop :=  λ (a : 𝒩) (n : ℕ), f a = n with hr,
    have g₁ : ∀ a : 𝒩, ∃ n : ℕ, R a n,
    {-- proof of ∀ a : 𝒩, ∃ n : ℕ, R a n
        intro a,
        use f a,
        rw hr,
    },
    have bcpa := (bcp R g₁) a, -- we use BCP here
    cases bcpa with m bcpa_m,
    cases bcpa_m with n bcpcon,
    cases exists_start_eq_ne a m with b hb,
    use b,
    split,
    {-- need to prove: a # b
        use m,
        exact hb.elim_right,
    },
    {-- need to prove: f a = f b
        have g₂ : R a n,
        {-- proof of g₂
            apply bcpcon a,
            intros i hi,
            refl,
        },
        have g₃ : R b n,
        {-- proof of g₃
            apply bcpcon b,
            intros i hi,
            exact hb.elim_left i hi,
        },
        rw hr at g₂ g₃,
        rwa [g₂, g₃],
    }
end

/-
The above theorem perhaps isn't how a classical mathematician would define "not injective"
This theorem should remove any doubts that the previous theorem shows
that the function is not injective
-/
theorem not_injective (f : 𝒩 → ℕ) : BCP → ¬(∀ a b : 𝒩, f a = f b → a =' b) :=
begin
    intros bcp h,
    have h0 := h nat_seq.zero,
    cases strongly_not_injective f bcp nat_seq.zero with b hb,
    have hb0 := h0 b hb.elim_right,
    exact (nat_seq.ne_of_apart _ _ hb.elim_left) hb0,
end

lemma grow_tail (a b : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, i >= nat.succ(n) → a i = b i)
    (h₂ : a n = b n) :
    ∀ i : ℕ, i >= n → a i = b i :=
begin
    intros i hi,
    rwa [ge_iff_le, le_iff_lt_or_eq] at hi,
    cases hi with lti eqi,
    {-- case: n < i
        apply h₁,
        rwa [ge_from_le, nat.succ_le_iff],
    },
    {-- case: n = i
        rw ← eqi,
        exact h₂,
    }
end

-- A lemma needed at the end of the next theorem
lemma tail_equal_not_forall_equal_implies_exists_ne (a b : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, i >= n → a i = b i)
    (h₂ : ¬ ∀ i : ℕ, a i = b i) :
    ∃ i : ℕ, i < n ∧ a i ≠ b i :=
begin
    induction n with m hm,
    {-- case: m = 0, this is impossible
        exfalso,
        apply h₂,
        intro i,
        have hi := h₁ i,
        apply hi,
        simp,
    },
    {-- case: m → m + 1
        have ambm := lt_trichotomy (a m) (b m),
        rwa [or_comm, or_assoc, ← ne_iff_lt_or_gt] at ambm,
        cases ambm with meq mne,
        {-- case: a m = b m
            have h₂ := grow_tail a b m h₁ meq,
            have h₃ := hm h₂,
            cases h₃ with i hi,
            use i,
            split,
            {-- need to prove: i < succ(m)
                transitivity m,
                exact hi.elim_left,
                exact nat.lt_succ_self m,
            },
            {-- need to prove: a i ≠ b i
                exact hi.elim_right,
            }
        },
        {-- case: a m ≠ b m
            use m,
            split,
            exact nat.lt_succ_self m, -- m < succ(m)
            exact ne.symm mne, -- a m ≠ b m
        }
    }
end

-- simple lemma needed for next theorem
lemma ite_cond_eq (a b d : 𝒩) (n : ℕ) (hd : d =' (λ i, ite (i < n) (b i) (a i))) : 
    ∀ (i : ℕ), i ≥ n → d i = a i :=
begin
    intros i hi,
    rw hd,
    simp,
    split_ifs,
    {-- case: i < n
        exfalso,
        exact (not_lt_of_ge hi) h,
    },
    {-- case: i ≥ n
        refl,
    }
end

/--
Another example to demonstrate the power of BCP
If two sequences are apart, then a third sequence cannot be equal to both
(and which sequence it is not equal to can be determined)
-/
theorem apart_iff_forall_ne_or_ne (bcp : BCP) (a b : 𝒩) : a # b ↔ ∀ c : 𝒩, a ≠' c ∨ c ≠' b :=
begin
    split,
    {-- need to prove: a # b → ∀ c : 𝒩, c ≠ a ∨ c ≠ b
        intros h c,
        cases nat_seq.apart_cotrans a b h c with hac hcb,
        {-- case: a # c
            left,
            exact nat_seq.ne_of_apart a c hac,
        },
        {-- case: c # b
            right,
            exact nat_seq.ne_of_apart c b hcb,
        }
    },
    {-- need to prove: (∀ c : 𝒩, c ≠ a ∨ c ≠ b) → a # b, BCP is needed here
        intro h,
        set R : 𝒩 → ℕ → Prop := λ c, λ n, if n = 0 then c ≠' a else c ≠' b with hR,
        have hz : 0 = 0 := rfl,
        have hr : ∀ c : 𝒩, ∃ n : ℕ, R c n, by 
        {-- need to prove: ∀ c : 𝒩, ∃ n : ℕ, R c n
            intro c,
            cases h c with hc₁ hc₂,
            {-- case: a ≠ c
                use 0,
                rw hR,
                split_ifs,
                rw nat_seq.ne_symm,
                exact hc₁,
            },
            {-- case: c ≠ b
                use 1,
            }
        },
        have bcpb := (bcp R hr) b,
        cases bcpb with m bcpbm,
        cases bcpbm with n bcpbmn,
        have hb₁ := bcpbmn b,
        have hb₂ : ∀ i : ℕ, i < m → b i = b i, by
        {-- need to prove ∀ i : ℕ, i < m → b i = b 
            intros i hi,
            refl,
        },
        have hb := hb₁ hb₂,
        have hn : n = 0, by
        {-- need to prove: n = 0
            cases nat.eq_zero_or_pos n with hn₁ hn₂,
            {-- case: n = 0
                exact hn₁,
            },
            {-- case: n > 0, impossible
                exfalso,
                rw hR at hb,
                have hn₃ := ne_of_gt hn₂,
                rw ne at hn₃,
                split_ifs at hb,
                apply hb,
                refl,
            }
        },
        rw hn at bcpbmn,
        set d : 𝒩 := λ i, if i < m then b i else a i with hd,
        have hd₁ := bcpbmn d,
        have hd₂ : ∀ i : ℕ, i < m → b i = d i, by
        {-- need to prove: ∀ i : ℕ, i < m → b i = d i
            intros i hi,
            rw hd,
            simp,
            split_ifs,
            refl,
        },
        have hd₃ := hd₁ hd₂,
        rw hR at hd₃,
        split_ifs at hd₃,
        rw nat_seq.ne at hd₃,
        rw nat_seq.eq at hd₃,
        rw function.funext_iff at hd,
        have h₀ := ite_cond_eq a b d m hd,
        cases tail_equal_not_forall_equal_implies_exists_ne d a m h₀ hd₃ with j hj,
        use j,
        rw (hd₂ j hj.elim_left),
        symmetry,
        exact hj.elim_right,
    }
end

theorem BCP_implies_not_LPO : BCP → ¬reckless.LPO :=
begin
    intros bcp lpo,
    set R : 𝒩 → ℕ → Prop := λ a, λ i, if i = 0 then ∀ n : ℕ, a n = 0 else ∃ n, a n ≠ 0 with hR,
    have hz : 0 = 0 := rfl,
    have hr : ∀ a : 𝒩, ∃ n : ℕ, R a n, by
    {
        intro a,
        cases lpo a with aeq0 ane0,
        {-- case: ∀ n : ℕ, a n = 0
            use 0,
            rw hR,
            split_ifs, --We only need to consider the case 0 = 0
            exact aeq0,
        },
        {-- case: ∃ n : ℕ, a n ≠ 0
            use 1,
            rw hR,
            split_ifs,
            {-- case: 1 = 0, impossible
                exfalso,
                exact nat.one_ne_zero h,
            },
            {-- case: ¬1 = 0, need to prove: ∃ n : ℕ, a n ≠ 0
                exact ane0,
            }
        }
    },
    have bcp_r_0 := (bcp R hr) nat_seq.zero,
    cases bcp_r_0 with m bcp_r_0₁,
    cases bcp_r_0₁ with n bcp_r_0₂,
    cases nat.eq_zero_or_pos n with hn₁ hn₂,
    {-- case: n = 0
        set b : 𝒩 := λ k, if k < m then 0 else 1 with hb,
        have bstart0 : (∀ (i : ℕ), i < m → nat_seq.zero i = b i), by
        {
            intros i hi,
            simp [nat_seq.zero, hb],
            split_ifs,
            refl,
        },
        have bcp_b := (bcp_r_0₂ b) bstart0,
        rwa [hR, hn₁] at bcp_b,
        split_ifs at bcp_b,
        {-- case: 0 = 0, need to prove: ∀ n : ℕ, b n = 0 leads to a contradiction
            have hm := bcp_b m,
            simp [hb] at hm,
            split_ifs at hm,
            {-- case: m < m, impossible
                revert h,
                exact irrefl m,
            },
            {-- case: ¬ m < m, need to prove: false, we use hm (1 = 0)
                exact nat.one_ne_zero hm,
            }
        },
    },
    {-- case: n > 0
        have h₀ := bcp_r_0₂ nat_seq.zero,
        have h₁ : (∀ i : ℕ, i < m → nat_seq.zero i = nat_seq.zero i), by simp,
        have h₂ := h₀ h₁,
        rw hR at h₂,
        split_ifs at h₂,
        {-- case: n = 0, impossible since we assumed n > 0
            exact (ne_of_gt hn₂) h,
        },
        {-- have: ∃ n, nat_seq.zero n ≠ 0, this is a contradiction with the definition of nat_seq.zero
            cases h₂ with k hk,
            apply hk,
            refl,
        }
    }
end

-- In essence, this is the same proof as the proof of BCP_implies_not_LPO, 
-- which becomes unnecessary since we have proven LPO → WLPO
theorem BCP_implies_not_WLPO : BCP → ¬reckless.WLPO :=
begin
    intros bcp wlpo,
    set R : 𝒩 → ℕ → Prop := λ a, λ i, if i = 0 then ∀ n : ℕ, a n = 0 else ¬∀ n : ℕ, a n = 0 with hR,
    have hz : 0 = 0 := rfl,
    have hr : ∀ a : 𝒩, ∃ n : ℕ, R a n, by
    {
        intro a,
        cases wlpo a with aeq0 naeq0,
        {-- case: ∀ n : ℕ, a n = 0
            use 0,
            rw hR,
            split_ifs, --We only need to consider the case 0 = 0
            exact aeq0,
        },
        {-- case: ¬∀ n : ℕ, a n = 0
            use 1,
        }
    },
    have bcp_r_0 := (bcp R hr) nat_seq.zero,
    cases bcp_r_0 with m bcp_r_0₁,
    cases bcp_r_0₁ with n bcp_r_0₂,
    cases nat.eq_zero_or_pos n with hn₁ hn₂,
    {-- case: n = 0
        set b : 𝒩 := λ k, if k < m then 0 else 1 with hb,
        have bstart0 : (∀ (i : ℕ), i < m → nat_seq.zero i = b i), by
        {
            intros i hi,
            simp [nat_seq.zero, hb],
            split_ifs,
            refl,
        },
        have bcp_b := (bcp_r_0₂ b) bstart0,
        rwa [hR, hn₁] at bcp_b,
        split_ifs at bcp_b,
        {-- case: 0 = 0, need to prove: ∀ n : ℕ, b n = 0 leads to a contradiction
            have hm := bcp_b m,
            simp [hb] at hm,
            split_ifs at hm,
            {-- case: m < m, impossible
                revert h,
                exact irrefl m,
            },
            {-- case: ¬ m < m, need to prove: false, we use hm (1 = 0)
                exact nat.one_ne_zero hm,
            }
        },
    },
    {-- case: n > 0
        have h₀ := bcp_r_0₂ nat_seq.zero,
        have h₁ : (∀ i : ℕ, i < m → nat_seq.zero i = nat_seq.zero i), by simp,
        have h₂ := h₀ h₁,
        rw hR at h₂,
        split_ifs at h₂,
        {-- case: n = 0, impossible since we assumed n > 0
            exact (ne_of_gt hn₂) h,
        },
        {-- have: ¬∀ n : ℕ, nat_seq.zero n = 0, this is a contradiction with the definition of nat_seq.zero
            apply h₂,
            intro i,
            refl,
        }
    }
end