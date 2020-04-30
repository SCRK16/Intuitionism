/-
This file defined finite sequences from {0, ..., n} to ℕ
-/

import data.fin
import ..Intuitionism.nat_seq

structure fin_seq := mk :: (len : ℕ) (seq : fin len → ℕ)

namespace fin_seq

def finitize (a : 𝒩) (n : ℕ) : fin_seq := {
    len := n,
    seq := λ i, a i
}

def is_initial_of (a : fin_seq) (b : 𝒩) := ∀ i : fin a.len, a.seq i = b i

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
                        simp,
                    end),
}

def extend_inf (a : fin_seq) (b : 𝒩) : 𝒩 :=
    λ i, if h : i < a.len
        then a.seq (fin.cast_le h i)
        else b (i - a.len)

def empty_seq : fin_seq := {
    len := 0,
    seq := λ i, 0
}

lemma empty_seq_eq {a : fin_seq} (ha : a.len = 0): 
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

end fin_seq

/-
def fin_seq' (n : ℕ) := fin n → ℕ

def finitize (a : 𝒩) (n : ℕ) : fin_seq n := λ i, a i

def is_initial_of_inf {n : ℕ} (a : fin_seq n) (b : 𝒩) := ∀ i : fin n, a i = b i

infix `⊑`:50 := is_initial_of_inf

lemma is_initial_of_self (a : 𝒩) {n : ℕ} : (finitize a n) ⊑ a :=
begin
    intro i,
    refl,
end

def shorten {m : ℕ} (a : fin_seq m) (n : ℕ) (h : n ≤ m) : fin_seq n :=
begin
    intro i,
    exact a (fin.cast_le h i),
end

def extend {n m : ℕ} (a : fin_seq n) (b : fin_seq m) : fin_seq (m + n) :=
    λ i, if h : i.val < n then a (fin.cast_le h i) else b (fin.sub_nat n i (not_lt.mp h))

def extend_inf {n : ℕ} (a : fin_seq n) (b : 𝒩) : 𝒩 :=
    λ i, if h : i < n then a (fin.cast_le h i) else b (i - n)

-- fin 0 contains no elements, so a function (fin 0 → ℕ) is always the empty sequence <>
def empty_seq : fin_seq 0 := λ i : fin 0, 0

def empty_fin_0 (i : fin 0) : false :=
begin
    have hi := i.is_lt,
    rw lt_iff_not_ge' at hi,
    apply hi,
    exact zero_le i.val,
end

lemma empty_eq (a : fin_seq 0): ∀ i, empty_seq i = a i :=
begin
    intro i,
    exfalso,
    exact empty_fin_0 i,
end

lemma empty_extend_eq_self (a : 𝒩) : extend_inf empty_seq a =' a :=
begin
    intro i,
    simp [extend_inf],
end
-/