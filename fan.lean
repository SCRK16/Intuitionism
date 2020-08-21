/-
This file captures the notions:
* Spread laws and spreads
* Fan laws and fans
* Bars
* The fan theorem, introduced as an axiom
-/

-- Decide: Use def / structure / class

import ..Intuitionism.bcp
import ..Intuitionism.fin_seq

open fin_seq

def is_spread_law (σ : fin_seq → ℕ) : Prop :=
    σ empty_seq = 0 ∧
    (∀ s : fin_seq, σ s = 0 ↔ ∃ n : ℕ, σ (extend s (singleton n)) = 0)

def is_fan_law (β : fin_seq → ℕ) : Prop :=
    is_spread_law β ∧
    (∀ s : fin_seq, (β s = 0 → ∃ n : ℕ, ∀ m : ℕ, β (extend s (singleton m)) = 0 → m ≤ n))

lemma fan_law_is_spread_law (β : fin_seq → ℕ) (hβ : is_fan_law β) : is_spread_law β := and.elim_left hβ

def spread (σ : fin_seq → ℕ) (hσ : is_spread_law σ) : Type := {a : 𝒩 // ∀ n : ℕ, σ (finitize a n) = 0}

def fan (β : fin_seq → ℕ) (hβ : is_fan_law β) : Type := {a : 𝒩 // ∀ n : ℕ, β (finitize a n) = 0}

lemma fan_is_spread (β : fin_seq → ℕ) (hβ : is_fan_law β) : fan β hβ = spread β (fan_law_is_spread_law β hβ) :=
begin
    rw fan,
    rw spread,
end

def is_bar (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : set fin_seq) : Prop :=
    ∀ a : fan β hβ, ∃ n : ℕ, finitize a.val n ∈ B

def fan_theorem (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : set fin_seq) (hB : is_bar β hβ B) : Prop :=
    ∃ m : ℕ, ∀ a : fan β hβ, ∃ n : ℕ, n ≤ m ∧ finitize a.val n ∈ B

-- Hard to use
def principle_of_bar_induction (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : set fin_seq) (hB : is_bar β hβ B) 
    (C : set fin_seq) (hC₁ : C ⊆ B)
    (hC₂ : ∀ s : fin_seq, (β s = 0 ∧ s ∈ C) → ∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C)
    (hC₃ : ∀ s : fin_seq, β s = 0 → (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) → s ∈ C)
    : Prop := empty_seq ∈ C