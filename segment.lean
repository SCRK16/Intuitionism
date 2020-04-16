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

def fst (s : 𝕊) : ℚ := (subtype.val s).fst

def snd (s : 𝕊) : ℚ := (subtype.val s).snd

def proper (s : 𝕊) : Prop := s.fst < s.snd

def contained (s t : 𝕊) : Prop := t.fst ≤ s.fst ∧ s.snd ≤ t.snd

infix `⊑`:50 := contained

def proper_contained (s t : 𝕊) : Prop := t.fst < s.fst ∧ s.snd < t.snd

infix `⊏`:50 := proper_contained

def lt (s t : 𝕊) : Prop := s.snd < t.fst

infix `<` := lt

def le (s t : 𝕊) : Prop := s.fst ≤ t.snd

infix `≤` := le

def inclusion (q : ℚ) : 𝕊 :=
    subtype.mk (q, q)
    begin
        refl,
    end

@[instance] def has_zero : has_zero 𝕊 := { zero := inclusion 0 }

@[trans] theorem contained_trans (s t v: 𝕊) (h₁ : s ⊑ t) (h₂ : t ⊑ v) : s ⊑ v :=
begin
    split,
    {-- need to prove: fst v ≤ fst s
        transitivity t.fst,
        exact h₂.elim_left,
        exact h₁.elim_left,
    },
    {-- need to prove: snd s ≤ snd v
        transitivity t.snd,
        exact h₁.elim_right,
        exact h₂.elim_right,
    }
end

@[refl] theorem contained_refl (s : 𝕊) : s ⊑ s :=
begin
    split,
    refl,
    refl,
end

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

@[trans] theorem lt_trans (s t v : 𝕊) (h₁ : s < t) (h₂ : t < v) : s < v :=
begin
    have ht := subtype.property t,
    have h₃ : s.snd < t.snd := lt_of_lt_of_le h₁ ht,
    rw segment.lt,
    transitivity t.snd,
    exact h₃,
    exact h₂,
end

@[refl] theorem le_refl (s : 𝕊) : s ≤ s :=
begin
    exact (subtype.property s),
end

/--
We say that two rational segments 'touch' if they partially cover eachother
-/
def touches (s t: 𝕊) : Prop := s ≤ t ∧ t ≤ s

infix `≈` := touches

@[refl] theorem touches_refl (s : 𝕊) : s ≈ s :=
begin
    split,
    refl,
    refl,
end

def add (s t : 𝕊) : 𝕊 := subtype.mk (s.fst + t.fst, s.snd + t.snd)
    begin
        apply add_le_add,
        exact subtype.property s,
        exact subtype.property t,
    end

theorem add_assoc (s t v : 𝕊) : add (add s t) v = add s (add t v) :=
begin
    repeat {rw add},
    rw subtype.mk_eq_mk,
    rw prod.mk.inj_iff,
    split,
    {
        repeat {rw fst},
        rw add_assoc,
        rw add_left_inj,
        refl,
    },
    {
        repeat {rw snd},
        rw add_assoc,
        rw add_left_inj,
        refl,
    }
end

theorem add_comm (s t : 𝕊) : add s t = add t s :=
begin
    rw add,
    rw add,
    apply subtype.eq,
    simp,
    split,
        exact rat.add_comm (fst s) (fst t),
        exact rat.add_comm (snd s) (snd t),
end

-- We use this lemma in proving that addition on ℛ is well-defined
lemma contained_bounds_le (s t : 𝕊) (h : s ⊑ t) : s.snd - s.fst ≤ t.snd - t.fst :=
begin
    rw contained at h,
    apply sub_le_sub,
    exact h.elim_right,
    exact h.elim_left,
end

instance : add_comm_semigroup 𝕊 :=
{
    add := segment.add, 
    add_assoc := segment.add_assoc,
    add_comm := segment.add_comm,
}

end segment