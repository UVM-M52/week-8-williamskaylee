-- Math 52: Week 8

import .utils
open classical

definition is_even (n : ℤ) : Prop := ∃ (k : ℤ), n = 2 * k

definition is_odd (n : ℤ) : Prop := ∃ (k : ℤ), n = 2 * k + 1

-- We will prove these two basic facts later in the course.
axiom is_not_even_iff_is_odd (n : ℤ) : ¬ is_even n ↔ is_odd n
axiom is_not_odd_iff_is_even (n : ℤ) : ¬ is_odd n ↔ is_even n

-- We proved this one before!
theorem even_square : ∀ (n : ℤ), is_even (n * n) ↔ is_even n :=
begin
intro n,
split,
{ by_contrapositive,
  intro H,
  rw is_not_even_iff_is_odd at H,
  rw is_not_even_iff_is_odd,
  cases H with k H,
  existsi (2*k*k + 2*k:ℤ),
  rw H,
  int_refl [k],
},
{ intro H,
  cases H with k H,
  existsi (2*k*k:ℤ),
  rw H,
  int_refl [k],
}
end

-- We proved this fact earlier!
theorem zero_or_zero_of_mul_zero : ∀ {a b : ℤ}, a * b = 0 → a = 0 ∨ b = 0 :=
begin
intros a b H,
by_trichotomy (a, (0:ℤ)),
{ intro Hazero,
  left,
  assumption,
},
{ intro Haneg,
  by_trichotomy (b, (0:ℤ)),
  { intro Hbzero,
    right,
    assumption,
  },
  { intro Hbneg,
    apply absurd H,
    apply ne_of_gt,
    apply mul_pos_of_neg_of_neg,
    assumption,
    assumption,
  },
  { intro Hbpos,
    apply absurd H,
    apply ne_of_lt,
    apply mul_neg_of_neg_of_pos,
    assumption,
    assumption,
  }
},
{ intro Hapos,
  by_trichotomy (b, (0:ℤ)),
  { intro Hbzero,
    right,
    assumption,
  },
  { intro Hbneg,
    apply absurd H,
    apply ne_of_lt,
    apply mul_neg_of_pos_of_neg,
    assumption,
    assumption,
  },
  { intro Hbpos,
    apply absurd H,
    apply ne_of_gt,
    apply mul_pos,
    assumption,
    assumption,
  }
},
end


-- This fact will be useful to prove the next theorem:
-- eq_of_sub_eq_zero (x y : ℤ) : x - y = 0 → x = y
theorem mul_left_cancel_of_nonzero {n : ℤ} : n ≠ 0 → (∀ {a b : ℤ}, n * a = n * b ↔ a = b) :=
begin
intros Hpos a b,
split,
{ sorry },
{ sorry },
end

-- This is the main theorem that shows √2 is irrational.
theorem main : ¬ ∃ (m n : ℤ), (is_odd n ∨ is_odd m) ∧ n * n = 2 * m * m :=
have L2 : (2:ℤ) ≠ 0 := nonzero_trivial 2,
begin
intro H,
cases H with m H,
cases H with n H,
cases H with Hodd H,
have Heven : is_even n,
begin
sorry,
end,
cases Hodd,
{ sorry },
{ sorry },
end