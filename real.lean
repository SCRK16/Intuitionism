import ..Intuitionism.segment

/--
We say that a sequence of segments is 'shrinking' if each segment is contained within its predecessor
-/
def shrinking (r : ℕ → 𝕊) := ∀ n, r (n + 1) ⊑ r n

/--
We say that a sequence of segments is 'dwindling' if we can make the segments arbitrarily small
-/
def dwindling (r : ℕ → 𝕊) := ∀ m : ℕ, ∃ n : ℕ, (r n).snd - (r n).fst < (1 / 2^m)

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

def lt (x y : ℛ) : Prop := ∃ n : ℕ, x.seq n < y.seq n

infix `<` := lt

def le (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≤ y.seq n

infix `≤` := le

def apart (x y : ℛ) : Prop := x < y ∨ y < x

def eq (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≈ y.seq n

infix `='`:50 := eq

def ne (x y : ℛ) : Prop := ¬ x =' y

infix `≠'`:50 := ne

end real_seq


/-
TODO:
1) Define inclusion from rationals intro reals using: ℚ → ℕ → 𝕊 := λ q, λ n, (q - 1 / 2^n, q + 1 / 2^n)
2) Define 0 using λ n, (0, 0)
3) Show that 0 in (2) and the embedding of 0 in (1) are equal
4) Theorems in 3.4 of int2
5) Intermediate Value Theorem and its constructive counterparts
6) Completeness of (ℛ, ≤)
7) Every real function is continuous
-/