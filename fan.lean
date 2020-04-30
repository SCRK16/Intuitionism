/-
This file captures the notions:
* Spread laws and spreads
* Fan laws and fans
* Bars
* The fan theorem, introduced as an axiom
-/

-- Decide: Use def / structure / class

import ..Intuitionism.fin_seq

open fin_seq

variables {β σ : fin_seq → ℕ}

def is_spread_law (σ : fin_seq → ℕ) : Prop := 
    σ empty_seq = 0 ∧
    (∀ s : fin_seq, σ s = 0 → ∃ n : ℕ, σ (extend s (singleton n)) = 0)

--TODO: Take another look at this
structure spread := mk :: 
    (σ : fin_seq → ℕ)
    (spread_law : is_spread_law σ)
    (spread := {a : 𝒩 // ∀ n : ℕ, σ (finitize a n) = 0})

def is_fan_law (β : fin_seq → ℕ) : Prop :=
    is_spread_law β ∧
    (∀ s : fin_seq, (β s = 0 → ∃ n : ℕ, ∀ m : ℕ, β (extend s (singleton m)) = 0 → m ≤ n))

--TODO: Take another look at this
structure fan := mk ::
    (β : fin_seq → ℕ)
    (fan_law : is_fan_law β)
    (fan := {a : 𝒩 // ∀ n : ℕ, β (finitize a n) = 0})

/-
-- This does not work, error: type expected at (F.fan) term has type ({a // ∀ (n : ℕ), F.β (finitize a n) = 0})
def is_bar (B : set fin_seq) (F : fan) : Prop := ∀ a : F.fan, ∃ n : ℕ, finitize (subtype.val a) n ∈ B
-/

variables {hβ : is_fan_law β}

def fan' (β : fin_seq → ℕ) (h : is_fan_law β) := {a : 𝒩 // ∀ n : ℕ, β (finitize a n) = 0}

#print fan'

def is_bar' (B : set fin_seq) : Prop :=
    ∀ a : fan' β hβ, ∃ n : ℕ, finitize a.val n ∈ B

#reduce is_bar'

#print is_bar'

def is_bar'' (B : set fin_seq) (F : Type) (hF : F = fan' β hβ) :=
    ∀ a : F, ∃ n : ℕ, finitize (eq.mp hF a).val n ∈ B

#print is_bar''

--∀ a : F, ∃ n : ℕ, finitize a.val n ∈ B


axiom fan_theorem (B : set fin_seq) (hB : @is_bar' β hβ B) :
    ∃ m : ℕ, ∀ a : fan' β hβ, ∃ n : ℕ, n ≤ m ∧ finitize a.val n ∈ B

--Error: a is not a subtype anymore
--def is_bar (B : set fin_seq) (F : fan) : Prop := ∀ a : F.fan, ∃ n : ℕ, finitize a.val n ∈ B