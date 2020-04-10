/-
This file defines rational segments 𝕊,
here defined as a subtype of ℚ × ℚ
Also defines relations on 𝕊, like ≤, ⊑ and ≈
-/

import data.rat
import algebra.order


/--
Rational segments 𝕊  
Each s in 𝕊 is a pair of rational numbers (p, q) such that p ≤ q  
Rational segments can be interpreted as intervals, [p, q], with rational end points
-/
def segment := {s : ℚ × ℚ // s.fst ≤ s.snd}

notation `𝕊` := segment

namespace segment

def fst : 𝕊 → ℚ :=
begin
    intro s,
    cases s with t ht,
    exact t.fst,
end

def snd : 𝕊 → ℚ :=
begin
    intro s,
    cases s with t ht,
    exact t.snd,
end

def proper (s : 𝕊) : Prop := s.fst < s.snd

def contained (s t : 𝕊) : Prop := s.fst ≤ t.fst ∧ s.snd ≤ t.snd

infix `⊑`:50 := contained

def proper_contained (s t : 𝕊) : Prop := t.fst < s.fst ∧ s.snd < t.snd

infix `⊏`:50 := proper_contained

def lt (s t : 𝕊) : Prop := s.snd < t.fst

infix `<` := lt

def le (s t : 𝕊) : Prop := s.fst ≤ t.snd

infix `≤` := le

-- This lemma immediately follows from a similar statement about ℚ
lemma le_iff_not_lt (s t : 𝕊) : s ≤ t ↔ ¬ t < s :=
begin
    split,
    {-- need to prove: s ≤ t → ¬ t < s
        intro h,
        apply not_lt_of_le,
        exact h,
    },
    {-- need to prove: ¬ t < s → s ≤ t
        intro h,
        apply le_of_not_lt,
        exact h,
    }
end

lemma lt_iff_not_le (s t : 𝕊) : s < t ↔ ¬ t ≤ s :=
begin
    split,
    {-- need to prove: s < t → ¬ t ≤ s
        intro h,
        apply not_le_of_lt,
        exact h,
    },
    {-- need to prove: ¬ t ≤ s → s < t
        intro h,
        apply lt_of_not_ge,
        rw ge_iff_le,
        exact h,
    }
end

/--
We say that two rational segments 'touch' if they partially cover eachother
-/
def touches (s t: 𝕊) : Prop := s ≤ t ∧ t ≤ s

infix `≈` := touches

end segment