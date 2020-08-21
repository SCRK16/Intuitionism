/-
This file captures the notion of a statement being reckless  
Meaning: A statement that cannot be proven, and whose negation also cannot be proven  

The most important example of recklessness is the law of exluded middle: ∀ P : Prop, P ∨ ¬ P,  
also called "the principle of omniscience"
-/

import ..Intuitionism.nat_seq
import ..Intuitionism.real
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
    intro po,
    intro a,
    cases po (∃ n : ℕ, a n ≠ 0) with h₁ h₂,
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
Double negation cannot simply be eliminated for all propositions P
Also shows that proof by contradiction cannot always be applied
-/
theorem reckless_not_not_implies : reckless_LPO (∀ P : Prop, ¬¬P → P) :=
begin
    split,
    {-- need to prove: PO → ∀ P : Prop, ¬¬P → P
        intros po P nnp,
        cases po P with hp np,
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
        apply PO_implies_LPO,
        intro P,
        apply h,
        exact not_not_em P,
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
        tauto,
    }
end

/--
Given a b : 𝒩, we already know that a < b → a ≤ b, and that a = b → a ≤ b  
However, this theorem shows that the opposite is not true  
One might expect a ≤ b → (a < b ∨ a = b),  
but this statement actually implies LPO, and is therefore reckless
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
        cases h₁ nat_seq.zero a (nat_seq.zero_le a) with zlt zeq,
        {-- case: 0 < a
            right,
            have h₂ := or.intro_left (a < nat_seq.zero) zlt,
            rw ← nat_seq.apart_iff_lt_or_lt at h₂,
            rw nat_seq.apart_symm at h₂,
            exact h₂,
        },
        {-- case: 0 = a
            left,
            exact nat_seq.eq_symm.mp zeq,
        }
    },
end

-- The two following theorems look funny together
theorem implies_not_implies_not : ∀ P Q : Prop, (P ∨ ¬P → ¬Q) → ¬Q :=
begin
    intros P Q h hq,
    have h₁ := mt h,
    have h₂ := h₁ (not_not_intro hq),
    exact (not_not_em P) h₂,
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

instance start_le_not_zero_decidable (a : 𝒩) (n : ℕ) : decidable (∃ i : ℕ, i ≤ n ∧ a i ≠ 0) :=
begin
    induction n with d hd,
    {
        simp only [nat.nat_zero_eq_zero, le_zero_iff_eq, exists_eq_left, ne.def],
        exact ne.decidable _ _,
    },
    {
        have hds : decidable (a (nat.succ d) ≠ 0) := ne.decidable _ _,
        have hdt : decidable ((∃ (i : ℕ), i ≤ d ∧ a i ≠ 0) ∨ a (nat.succ d) ≠ 0), by 
        {
            exact @or.decidable (∃ (i : ℕ), i ≤ d ∧ a i ≠ 0) (a (nat.succ d) ≠ 0) hd hds, 
        },
        have hiff : ((∃ (i : ℕ), i ≤ d ∧ a i ≠ 0) ∨ a (nat.succ d) ≠ 0) ↔ (∃ (i : ℕ), i ≤ nat.succ d ∧ a i ≠ 0), by
        {
            split,
            {-- need to prove: →
                intro h,
                cases h with ilt ieq,
                {-- case: ∃ (i : ℕ), i ≤ d ∧ a i ≠ 0
                    cases ilt with i hi,
                    use i,
                    split,
                    {-- need to prove: i ≤ nat.succ d
                        exact le_trans hi.elim_left (nat.le_succ d),
                    },
                    {-- need to prove: a i ≠ 0
                        exact hi.elim_right,
                    }
                },
                {-- case: a (nat.succ d) ≠ 0
                    use nat.succ d,
                    split,
                    {-- need to prove: nat.succ d ≤ nat.succ d
                        refl,
                    },
                    {-- need to prove: a (nat.succ d) ≠ 0
                        exact ieq,
                    }
                }
            },
            {-- need to prove: ←
                intro h,
                cases h with i hi,
                cases lt_or_eq_of_le hi.elim_left with ilt ieq,
                {-- case: i < nat.succ d
                    left,
                    use i,
                    split,
                    {-- need to prove: i ≤ d
                        exact nat.le_of_lt_succ ilt,
                    },
                    {-- need to prove: a i ≠ 0
                        exact hi.elim_right,
                    }
                },
                {-- case: i = nat.succ d
                    right,
                    rw ← ieq,
                    exact hi.elim_right,
                }
            },
        },
        apply decidable_of_decidable_of_iff hdt hiff,
    }
end

instance start_lt_not_zero_decidable (a : 𝒩) (n : ℕ) : decidable (∃ i : ℕ, i < n ∧ a i ≠ 0) :=
begin
    induction n with d hd,
    {
        apply is_false,
        intro h,
        cases h with i hi,
        exact (nat.not_lt_zero i) hi.elim_left,
    },
    {
        cases hd with hdfalse hdtrue,
        {-- case: ¬∃ (i : ℕ), i < d ∧ a i ≠ 0
            have hds : decidable (a d ≠ 0) := ne.decidable _ _,
            cases hds with hdsfalse hdstrue,
            {-- case: ¬a d ≠ 0
                apply is_false,
                intro h,
                cases h with i hi,
                cases lt_or_eq_of_le (nat.le_of_lt_succ hi.elim_left) with iltd ieqd,
                {-- case: i < d
                    apply hdfalse,
                    use i,
                    exact and.intro iltd hi.elim_right,
                },
                {-- case: i = d
                    rw ieqd at hi,
                    exact hdsfalse hi.elim_right,
                }
            },
            {-- case: a d ≠ 0
                apply is_true,
                use d,
                exact and.intro (lt_add_one d) hdstrue,
            }
        },
        {-- case: ∃ (i : ℕ), i < d ∧ a i ≠ 0
            apply is_true,
            cases hdtrue with i hi,
            use i,
            split,
            {-- need to prove: i < nat.succ d
                exact lt_trans hi.elim_left (lt_add_one d),
            },
            {-- need to prove: a i ≠ 0
                exact hi.elim_right,
            }
        }
    }
end

def snap (a : 𝒩) : ℛ := subtype.mk (λ n : ℕ, if h : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
    then segment.inclusion (1 / nat.succ (nat.find h))
    else segment.two_sided_inclusion (1 / nat.succ n) 
        begin 
        -- need to prove: 1/n > 0
            simp [nat.zero_lt_succ, nat.cast_add_one_pos],
        end)
    begin
    -- need to prove: The function defined above is a real number: It shrinks and it dwindles
        split,
        {-- need to prove: shrinking
            rw shrinking,
            intro n,
            split_ifs with h₁ h₂,
            {-- case: (∃ i ≤ n+1, a i ≠ 0) ∧ (∃ i ≤ n, a i ≠ 0)
                suffices hh : nat.find h₁ = nat.find h₂,
                {-- need to prove: nat.find h₁ = nat.find h₂ → shrinking
                    rw hh,
                },
                {-- need to prove: nat.find h₁ = nat.find h₂
                    have hh₁ := nat.find_spec h₁,
                    have hh₂ := nat.find_spec h₂,
                    cases lt_trichotomy (nat.find h₁) (nat.find h₂) with hlt hge,
                    {-- case: nat.find h₁ < nat.find h₂
                        exfalso,
                        apply nat.find_min h₂ hlt,
                        split,
                        {-- need to prove: nat.find h₁ ≤ n
                            transitivity (nat.find h₂),
                            exact (le_of_lt hlt),
                            exact hh₂.elim_left,
                        },
                        {-- need to prove: a (nat.find h₁) ≠ 0
                            exact hh₁.elim_right,
                        }
                    },
                    {
                        cases hge with heq hgt,
                        {-- case: nat.find h₁ = nat.find h₂
                            exact heq,
                        },
                        {-- case: nat.find h₂ > nat.find h₁
                            exfalso,
                            apply nat.find_min h₁ hgt,
                            split,
                            {-- need to prove: nat.find h₂ ≤ n + 1
                                transitivity n,
                                exact hh₂.elim_left,
                                exact nat.le_succ n,
                            },
                            {-- need to prove: a (nat.find h₂) ≠ 0
                                exact hh₂.elim_right,
                            }
                        }
                    }
                }
            },
            {-- case: (∃ i ≤ n+1, a i ≠ 0) ∧ ¬(∃ i ≤ n, a i ≠ 0)
                dsimp [segment.inclusion, segment.two_sided_inclusion, segment.contained, segment.fst, segment.snd],
                split,
                {-- need to prove: -(1/(↑n+1)) ≤ 1/(↑(nat.find h₁) + 1)
                    transitivity (rat.mk 0 1),
                    repeat {
                        rw rat.zero_mk 1,
                        simp [le_of_lt, nat.cast_add_one_pos],
                    },
                },
                {-- need to prove: 1/(↑(nat.find h₁) + 1) ≤ (1/(↑n+1))
                    cases lt_or_eq_of_le (nat.find_spec h₁).elim_left with hlt heq,
                    {-- case: nat.find h₁ < n + 1
                        exfalso,
                        apply h₂,
                        use nat.find h₁,
                        split,
                        {-- need to prove: nat.find h₁ ≤ n
                            exact nat.lt_succ_iff.mp hlt,
                        },
                        {-- need to prove: a (nat.find h₁) ≠ 0
                            exact (nat.find_spec h₁).elim_right,
                        }
                    },
                    {-- case: nat.find h₁ = n + 1
                        rw heq,
                        rw one_div_le_one_div,
                        {-- need to prove: n + 1 ≤ n + 1 + 1
                            simp,
                        },
                        {-- need to prove: 0 ≤ n + 1
                            exact nat.cast_add_one_pos _,
                        },
                        {-- need to prove: 0 ≤ n + 1 + 1
                            exact nat.cast_add_one_pos _,
                        }
                    }                    
                }
            },
            {-- case: ¬(∃ i ≤ n+1, a i ≠ 0) ∧ (∃ i ≤ n, a i ≠ 0)
                exfalso,
                cases h with i hi,
                apply h₁,
                use i,
                split,
                {-- need to prove: i < n + 1
                    transitivity n,
                    exact hi.elim_left,
                    exact nat.le_succ n,
                },
                {-- need to prove: a i ≠ 0
                    exact hi.elim_right,
                }
            },
            {-- case: ¬(∃ i ≤ n+1, a i ≠ 0) ∧ ¬(∃ i ≤ n, a i ≠ 0)
                apply segment.two_sided_inclusion_contained,
                rw one_div_le_one_div,
                {-- need to prove: ↑(nat.succ n) ≤ ↑(nat.succ (n + 1))
                    simp,
                },
                {-- need to prove: 0 < ↑(nat.succ (n+1))
                    transitivity (↑n + 1 : ℚ),
                    exact nat.cast_add_one_pos n,
                    simp [zero_lt_one],
                },
                {-- need to prove: 0 < ↑(nat.succ n)
                    exact nat.cast_add_one_pos n,
                }
            }
        },
        {-- need to prove: Dwindling
            rw dwindling,
            intros q hq,
            dsimp [segment.inclusion, segment.two_sided_inclusion, segment.snd, segment.fst],
            sorry,
        }
    end 

theorem reckless_LPO_real_lt_eq_gt : reckless_LPO (∀ x y : ℛ, x < y ∨ x =' y ∨ y < x) :=
begin
    split,
    {
        intros po x y,
        cases po (x < y) with xlt nxlt,
        {-- case: x < y
            left,
            exact xlt,
        },
        {-- case: ¬x < y
            right,
            cases po (y < x) with xgt nxgt,
            {-- case: y < x
                right,
                exact xgt,
            },
            {-- case: ¬y < x
                left,
                rw ← real_seq.le_iff_not_lt at *,
                exact real_seq.eq_of_le_of_le _ _ nxgt nxlt,
            }
        }
    },
    {-- need to prove: (∀ x : ℛ, x < y ∨ x =' y ∨ y < x) → LPO
        intros h a,
        have hsnap := h (snap a) (real_seq.inclusion_const 0),
        cases hsnap with hlt hge,
        {-- case: snap a < 0
            exfalso,
            cases hlt with n hn,
            simp [real_seq.seq, real_seq.inclusion_const, segment.inclusion, snap,
                segment.two_sided_inclusion, segment.lt, segment.fst, segment.snd] at hn,
            split_ifs at hn,
            {-- case: ∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                apply not_le_of_lt hn,
                simp [le_of_lt, nat.cast_add_one_pos],
            },
            {-- case: ¬∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                apply not_le_of_lt hn,
                simp [le_of_lt, nat.cast_add_one_pos],
            }
        },
        {
            cases hge with heq hgt,
            {-- case: snap a = 0
                left,
                intro n,
                have hn := heq n,
                simp [real_seq.seq, segment.touches, segment.le, segment.fst, segment.snd,
                    real_seq.seq, real_seq.inclusion_const, segment.inclusion, snap, segment.two_sided_inclusion] at hn,
                cases hn with hn₁ hn₂,
                split_ifs at hn₁,
                {-- case: ∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                    exfalso,
                    apply not_lt_of_le hn₁,
                    simp [nat.cast_add_one_pos],
                },
                {-- case: ¬∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                    have han := (forall_not_of_not_exists h_1) n,
                    simp at han,
                    exact han,
                }
            },
            {-- case: snap a > 0
                right,
                cases hgt with n hn,
                simp [real_seq.seq, real_seq.inclusion_const, segment.inclusion, snap,
                    segment.two_sided_inclusion, segment.lt, segment.fst, segment.snd] at hn,
                split_ifs at hn,
                {-- case: ∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                    cases h_1 with i hi,
                    use i,
                    exact hi.elim_right,
                },
                {-- case: ¬∃ i : ℕ, i ≤ n ∧ a i ≠ 0
                    exfalso,
                    rwa [lt_neg, neg_zero] at hn,
                    apply not_le_of_lt hn,
                    simp [le_of_lt, nat.cast_add_one_pos],
                }
            }
        }
    }
end

def WLEM : Prop := ∀ P : Prop, ¬P ∨ ¬¬P

def WLPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (¬∀ n : ℕ, a n = 0)

theorem PO_implies_WLEM : PO → WLEM :=
begin
    intros po P,
    cases po P with hp np,
    {-- case: P
        right, -- need to prove: ¬¬P
        intro np,
        exact np hp,
    },
    {-- case: ¬P
        left, -- need to prove: ¬P
        exact np,
    }
end

theorem LPO_implies_WLPO : LPO → WLPO :=
begin
    intros lpo a,
    cases lpo a with aeq ane,
    {-- case: ∀ n : ℕ, a n = 0
        left, -- need to prove: ∀ n : ℕ, a n = 0
        exact aeq,
    },
    {-- case: ∃ n : ℕ, a n ≠ 0
        right, -- need to prove: ¬∀ n : ℕ, a n = 0
        intro aeq,
        cases ane with n hn,
        exact hn (aeq n),
    }
end

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
    {-- case: ¬¬∃ (n : ℕ), a n = 0
        right,
        intro h,
        apply nnh,
        intro nex,
        cases nex with n nhn,
        exact nhn (h n),
    }
end

theorem weak_LPO_implies_LLPO : WLPO → LLPO :=
begin
    intros wlpo a,
    set d : 𝒩 := λ n, if n % 2 = 0 then if (∃ i : ℕ, i < n ∧ a i ≠ 0) then 0 else a n else 0 with ddef,
    cases wlpo d with deq nd,
    {-- case: ∀ n : ℕ, d n = 0
        right,
        intros k hk, -- need to prove: k % 2 = 1
        have hdk := deq k,
        rw ddef at hdk,
        simp at hdk,
        rw ← nat.mod_two_ne_zero,
        intro hkm,
        split_ifs at hdk,
        {-- case: ∃ i : ℕ, i < k ∧ a i ≠ 0
            cases h with i hi,
            apply hi.elim_right,
            exact hk.elim_left i hi.elim_left,
        },
        {-- case: ¬∃ i : ℕ, i < k ∧ a i ≠ 0 and a k = 0
            exact hk.elim_right hdk,
        }
    },
    {-- case: ¬∀ n : ℕ, d n = 0
        left,
        intros k hk, -- need to prove: k % 2 = 0
        rw ← nat.mod_two_ne_one,
        intro hkm,
        apply nd,
        intro n,
        rw ddef,
        simp,
        split_ifs,
        {-- need to prove: 0 = 0
            refl,
        },
        {-- need to prove: a n = 0, using n % 2 = 0 and ∀ x : ℕ, x < n → a x = 0
            simp at h_1,
            cases nat.lt_trichotomy n k with nlt nge,
            {-- case: n < k
                exact hk.elim_left n nlt,
            },
            {-- case: n ≥ k
                cases nge with neq ngt,
                {-- case: n = k
                    exfalso,
                    rwa [← nat.mod_two_ne_one, neq] at h,
                    exact h hkm,
                },
                {-- case: n > k
                    exfalso,
                    apply hk.elim_right,
                    exact h_1 k ngt,
                }
            }
        },
        {-- need to prove: 0 = 0
            refl,
        }
    }
end

theorem weak_LEM_implies_LLPO : WLEM → LLPO := 
begin
    intro wlem,
    apply weak_LPO_implies_LLPO,
    exact weak_LEM_implies_weak_LPO wlem,
end

-- We can also prove the above statement directly
theorem weak_LEM_implies_LLPO' : WLEM → LLPO := 
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
        have h₂ := h₁ P (¬P) (not_not_em P),
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
        exact h P (¬P) (and_not_self P).mp,
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
    exact h (P ∨ ¬P) (not_not_em P),
end

end reckless