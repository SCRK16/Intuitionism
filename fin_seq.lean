/-
This file defines finite sequences from {0, ..., n} to ℕ
-/

import data.fin
import tactic
import ..Intuitionism.nat_seq

@[ext] structure fin_seq := mk :: (len : ℕ) (seq : fin len → ℕ)

namespace fin_seq

def finitize (a : 𝒩) (n : ℕ) : fin_seq := {
    len := n,
    seq := λ i, a i.val
}

lemma finitize_len (a : 𝒩) (n : ℕ) : (finitize a n).len = n := rfl

def is_initial_of (a : fin_seq) (b : 𝒩) : Prop := ∀ i : fin a.len, a.seq i = b i

infix `⊑`:50 := is_initial_of

lemma is_initial_of_self (a : 𝒩) {n : ℕ} : (finitize a n) ⊑ a :=
begin
    intro i,
    refl,
end

def shorten (a : fin_seq) (m : ℕ) (h : m ≤ a.len) : fin_seq := {
    len := m,
    seq := λ i, a.seq (fin.cast_le h i)
}

def extend (a b : fin_seq) : fin_seq := {
    len := a.len + b.len,
    seq := λ i, if h : i.val < a.len
                then a.seq (fin.cast_le h i)
                else b.seq (fin.sub_nat a.len (fin.cast (add_comm a.len b.len) i)
                    begin -- need to prove: a.len ≤ (fin.cast _ i).val
                        rw not_lt at h,
                        transitivity i.val,
                        exact h,
                        refl,
                    end),
}

def extend_inf (a : fin_seq) (b : 𝒩) : 𝒩 :=
    λ i, if h : i < a.len
        then a.seq (fin.cast_le h i)
        else b (i - a.len)

lemma extend_inf_eq {a : fin_seq} {b₁ b₂ : 𝒩} (h : b₁ =' b₂) : extend_inf a b₁ =' extend_inf a b₂ :=
begin
    intro n,
    rwa [extend_inf, extend_inf],
    dsimp only [],
    split_ifs,
    {-- case: n < a.len
        refl,
    },
    {-- case: ¬n < a.len
        exact h (n - a.len),
    }
end

lemma eq_extend_inf {a₁ a₂ : fin_seq} {b : 𝒩} (h₁ : a₁.len = a₂.len) 
    (h₂ : ∀ i, a₁.seq i = a₂.seq (fin.cast h₁ i)) :
    extend_inf a₁ b =' extend_inf a₂ b :=
begin
    intro n,
    rwa [extend_inf, extend_inf],
    dsimp only [],
    split_ifs with g₁ g₂ g₃,
    {-- case: n < a₁.len ∧ n < a₂.len
        simp [h₂],
        refl,
    },
    {-- case: n < a₁.len ∧ ¬n < a₂.len
        exfalso,
        rw h₁ at g₁,
        exact g₂ g₁,
    },
    {-- case: ¬n < a₁.len ∧ n < a₂.len
        exfalso,
        rw h₁ at g₁,
        exact g₁ g₃,
    },
    {-- case: ¬n < a₁.len ∧ ¬n < a₂.len
        rw h₁,
    }
end

def empty_seq : fin_seq := {
    len := 0,
    seq := λ i, 0
}

lemma empty_seq_eq {a : fin_seq} (ha : a.len = 0) : 
    ∀ i, empty_seq.seq i = a.seq (fin.cast (
        begin -- need to prove: empty_seq.len = a.len (note: both are 0)
            rw ha,
            refl,
        end
    ) i) :=
begin
    intro i,
    exfalso,
    have hi := i.is_lt,
    rw lt_iff_not_ge' at hi,
    apply hi,
    exact zero_le i.val,
end

lemma empty_extend_eq_self (a : 𝒩) : extend_inf empty_seq a =' a :=
begin
    intro i,
    simp [extend_inf],
    split_ifs,
    {-- case: i < empty_seq.len, impossible since empty_seq.len = 0
        exfalso,
        rw lt_iff_not_ge' at h,
        apply h,
        exact zero_le i,
    },
    {-- need to prove: a (i - empty_seq.len) = a i
        refl, -- uses: by definition, empty_seq.len = 0 and i - 0 = i
    }
end

def singleton (n : ℕ) : fin_seq := {
    len := 1,
    seq := λ i, n
}

theorem finitize_initial_iff_start_eq (a b : 𝒩) (n : ℕ) : finitize a n ⊑ b ↔ (∀ j : ℕ, j < n → a j = b j) :=
begin
    split,
    {-- need to prove: finitize a n ⊑ b → (∀ j : ℕ, j < n → a j = b j)
        intros h j hj,
        exact h (fin.mk j hj),
    },
    {-- need to prove: (∀ j : ℕ, j < n → a j = b j) → finitize a n ⊑ b
        intros h i,
        exact h i i.is_lt,
    }
end

theorem finitize_eq_iff_start_eq (a b : 𝒩) (n : ℕ) : finitize a n = finitize b n ↔ (∀ j : ℕ, j < n → a j = b j) :=
begin
    split,
    {-- need to prove: finitize a n = finitize b n → (∀ j : ℕ, j < n → a j = b j)
        intros h j hj,
        rwa [finitize, finitize] at h,
        simp at h,
        rw function.funext_iff at h,
        exact h (fin.mk j hj),
    },
    {-- finitize a n = finitize b n ← (∀ j : ℕ, j < n → a j = b j)
        intro h,
        rwa [finitize, finitize],
        simp,
        rw function.funext_iff,
        intro i,
        exact h i.val i.is_lt,
    }
end

lemma finitize_initial_iff_finitize_eq (a b : 𝒩) (n : ℕ) : finitize a n ⊑ b ↔ finitize a n = finitize b n :=
begin
    rw finitize_eq_iff_start_eq,
    rw finitize_initial_iff_start_eq,
end

/-
The tail of the sequence a
If a is the empty sequence, then the result will be the empty sequence
-/
def tail (a : fin_seq) : fin_seq := {
    len := a.len - 1,
    seq := λ i, a.seq (fin.cast_le (nat.pred_le (nat.sub a.len 0)) i)
}

lemma tail_singleton_len_zero : ∀ n : ℕ, (tail (singleton n)).len = 0 :=
begin
    intro n,
    refl,
end

end fin_seq


-- Finite sequences with a fixed length
def len_seq (n : ℕ) : Type := fin n → ℕ

namespace len_seq

def to_fin_seq {n : ℕ} : len_seq n → fin_seq := λ f, {
    len := n,
    seq := f,
}

lemma fin_len_eq {n : ℕ} {a : len_seq n} : (to_fin_seq a).seq = a :=
begin
    refl,
end

lemma len_fin_eq (a : fin_seq) : (to_fin_seq a.seq) = a :=
begin
    cases a,
    refl,
end

lemma len_seq_0_unique (x y : len_seq 0) : x = y :=
begin
    rw function.funext_iff,
    intro a,
    exfalso,
    have h : 0 ≤ a.val := zero_le a.val,
    rw ← not_lt at h,
    exact h a.is_lt,
end

end len_seq