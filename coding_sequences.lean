import data.fin
import ..Intuitionism.nat_seq
import ..Intuitionism.fin_seq
import data.nat.pairing
import data.equiv.basic
import data.equiv.nat

--def code : fin_seq → ℕ := λ b : fin_seq, if b.len = 0 then 0 else nat.mkpair (b.seq 0) (code (fin_seq.tail b)) + 1

lemma len_seq_1_equiv_nat : len_seq 1 ≃ ℕ := {
    to_fun := λ a, a (fin.mk 0 nat.succ_pos'),
    inv_fun := λ n, λ i, n,
    left_inv := begin
        intro a,
        rw function.funext_iff,
        intro i,
        have hi : i = fin.mk 0 nat.succ_pos', by {
            rw fin.eq_iff_veq,
            have h := nat.le_of_lt_succ i.is_lt,
            rw nat.le_zero_iff at h,
            exact h,
        },
        rw hi,
    end,
    right_inv := begin
        intro n,
        refl,
    end
}

lemma len_seq_0_equiv_punit : len_seq 0 ≃ punit := {
    to_fun := λ a, punit.star,
    inv_fun := λ x, λ i, 0,
    left_inv := begin
        intro x,
        rw function.funext_iff,
        intro a,
        exfalso,
        have h : 0 ≤ a.val := zero_le a.val,
        rw ← not_lt at h,
        exact h a.is_lt,
    end,
    right_inv := begin
        intro x,
        exact punit_eq punit.star x,
    end
}

lemma len_seq_succ_equiv_len_seq (n : ℕ) : len_seq (nat.succ (nat.succ n)) ≃ len_seq (nat.succ n) := {
    to_fun := λ a, λ i, if i.val = n 
        then nat.mkpair
            (a ⟨n, lt.trans (lt_add_one n) (lt_add_one (nat.succ n))⟩) 
            (a ⟨nat.succ n, lt_add_one _⟩)
        else a ⟨i.val,
                begin 
                    have hi := i.is_lt,
                    exact nat.lt.step hi,
                end⟩,
    inv_fun := λ a, λ i, if h₁ : i.val < n 
        then a (fin.cast_lt i (nat.lt.step h₁)) 
        else if h₂ : i.val = n
            then (nat.unpair (a ⟨i.val, begin rw h₂, exact lt_add_one n, end⟩)).1
            else (nat.unpair (a ⟨i.val - 1, 
                begin
                    have hi : i.val = nat.succ n, by {
                        cases lt_or_eq_of_le (nat.le_of_lt_succ i.is_lt) with hlt heq,
                        exfalso,
                        cases lt_or_eq_of_le (nat.le_of_lt_succ hlt) with hlt₁ heq₁,
                            exact h₁ hlt₁,
                            exact h₂ heq₁,
                        exact heq,
                    },
                    rw hi,
                    exact lt_add_one (nat.succ n - 1),
                end⟩)).2,
    left_inv := begin
        rw function.left_inverse,
        intro a,
        rw function.funext_iff,
        intro i,
        split_ifs,
        {-- case: i.val < n ∧ i.val = n
            exfalso,
            have hi : i.val ≠ n := ne_of_lt h,
            have hi₁ : i.val = n, by {
                exact congr_fun (false.rec (fin.val = λ (i : fin (nat.succ (nat.succ n))), n) (hi h_1)) i,
            },
            exact hi hi₁,
        },
        {-- case: i.val < n
            have hi : (⟨(fin.cast_lt i _).val, _⟩ : fin (nat.succ (nat.succ n))) = i, by {
                rw fin.eq_iff_veq,
                apply fin.cast_lt_val,
            },
            rw hi,
        },
        {-- case: i.val = n
            rw nat.unpair_mkpair,
            dsimp only,
            have hi : (⟨n, _⟩ : fin (nat.succ (nat.succ n))) = i, by {
                rw fin.eq_iff_veq,
                rw h_1,
            },
            rw hi,
        },
        {-- case: i.val = nat.succ n
            rw nat.unpair_mkpair,
            dsimp only,
            have hi : (⟨nat.succ n, _⟩ : fin (nat.succ (nat.succ n))) = i, by {
                rw fin.eq_iff_veq,
                dsimp only,
                symmetry,
                rw nat.sub_eq_iff_eq_add at h_2,
                exact h_2,
                apply le_of_not_lt,
                intro h₁,
                cases lt_or_eq_of_le (nat.le_of_lt_succ h₁) with ilt0 ieq0,
                {-- case: i.val < 0
                    exact (nat.not_lt_zero i.val) ilt0,
                },
                {-- case: i.val = 0
                    cases n,
                    {-- case: n = 0
                        exact h_1 ieq0,
                    },
                    {-- case: nat.succ n
                        apply h,
                        rw ieq0,
                        exact nat.succ_pos n,
                    }
                }
            },
            rw hi,
        },
        {-- case: ¬i.val < nat.succ (nat.succ n)
            exfalso,
            cases lt_or_eq_of_le (nat.le_of_lt_succ i.is_lt) with hilt hieq,
            {-- case: i.val < nat.succ n
                cases lt_or_eq_of_le (nat.le_of_lt_succ hilt) with hilt₁ hieq₁,
                {
                    exact h hilt₁,
                },
                {
                    exact h_1 hieq₁,
                }
            },
            {-- case: i.val = nat.succ n
                apply h_2,
                rw hieq,
                rw nat.succ_sub_succ_eq_sub,
                refl,
            }
        },
    end,
    right_inv := begin
        rw function.right_inverse,
        rw function.left_inverse,
        intro a,
        rw function.funext_iff,
        intro i,
        simp,
        split_ifs,
        {-- case: nat.succ n < n
            exfalso,
            exact nat.not_succ_lt_self h_1,
        },
        {-- case: nat.succ n = n
            exfalso,
            apply nat.not_succ_le_self n,
            exact le_of_eq h_2,
        },
        {-- case: i.val = n
            rw nat.mkpair_unpair,
            have hi : (⟨n, _⟩ : fin (nat.succ n)) = i, by {
                rw fin.eq_iff_veq,
                symmetry,
                exact h,
            },
            rw hi,
        },
        {-- case: i.val < n
            have hi : ((fin.cast_lt ⟨i.val, _⟩ _) : fin (nat.succ n)) = i, by {
                rw fin.eq_iff_veq,
                apply fin.cast_lt_val,
            },
            rw hi,
        },
        {-- case: ¬i.val < (nat.succ n)
            exfalso,
            cases lt_or_eq_of_le (nat.le_of_lt_succ i.is_lt) with hilt hieq,
            {-- case: i.val < n
                exact h_1 hilt,
            },
            {-- case: i.val = n
                exact h hieq,
            }
        }
    end
}

theorem len_seq_equiv_nat (n : ℕ) : len_seq (nat.succ n) ≃ ℕ :=
begin
    induction n with d hd,
    {-- need to prove: len_seq 1 ≃ ℕ
        exact len_seq_1_equiv_nat,
    },
    {-- need to prove: (len_seq (nat.succ d) ≃ ℕ) → (len_seq (nat.succ (nat.succ d)) ≃ ℕ)
        transitivity len_seq (nat.succ d),
        {-- need to prove: len_seq (nat.succ (nat.succ d)) ≃ len_seq (nat.succ d)
            exact len_seq_succ_equiv_len_seq d,
        },
        {-- need to prove: len_seq (nat.succ d) ≃ ℕ, this is the induction hypothesis
            exact hd,
        }
    }
end

theorem len_seq_equiv_nat' (n : ℕ) (h : ¬n = 0) : len_seq n ≃ ℕ :=
begin
    have hz := zero_lt_iff_ne_zero.mpr h,
    have hn : n = nat.succ (n-1), by {
        cases n with d hd,
        {-- case: 0
            exfalso,
            apply h,
            refl,
        },
        {-- case: nat.succ n
            refl,
        }
    },
    rw hn,
    exact len_seq_equiv_nat (n-1),
end

-- Problem: Equality for fin_seq impossible since fin n → ℕ is not the same type as fin m → ℕ, even when n = m
theorem fin_seq_equiv_of_nat : fin_seq ≃ ℕ := {
    to_fun := λ a, if h : a.len = 0 then 0 else (nat.mkpair a.len ((len_seq_equiv_nat' a.len h).to_fun a.seq)) + 1,
    inv_fun := λ n, if h : n = 0
    then fin_seq.empty_seq
    else if h₁ : (nat.unpair (n-1)).1 = 0 then fin_seq.empty_seq
    else len_seq.to_fin_seq ((len_seq_equiv_nat' (nat.unpair (n-1)).1 h₁).inv_fun (nat.unpair (n-1)).2),
    left_inv := begin
        rw function.left_inverse,
        intro a,
        split_ifs,
        {-- case: a.len = 0
            have hlen : fin_seq.empty_seq.len = a.len, by {
                rw h,
                refl,
            },
            cases a,
            cases fin_seq.empty_seq,
            ext,
            {
                exact hlen,
            },
            {
                simp at hlen,
                sorry,
            }
        },
        {-- case: ¬a.len = 0
            sorry,
        }
    end,
    right_inv := begin
        rw function.right_inverse,
        rw function.left_inverse,
        intro n,
        split_ifs,
        {-- case: n = 0
            rw h,
            split_ifs,
            {
                exact h_1,
            },
            {
                exfalso,
                apply h_1,
                refl,
            }
        },
        {-- case: ¬n = 0
            sorry,
        }
    end
}