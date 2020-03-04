-- Math 52: Cheatsheet

--------------------------------
-- BASIC GOAL TRANSFORMATIONS --
--------------------------------

-- Conjunctive Goal
-- Use `split`:
example (P Q : Prop) : P ∧ Q :=
begin
split,
-- you can use braces to separate the two resulting goals
{ sorry },
{ sorry },
end

-- Disjunctive Goal
-- Use `left` or `right` to pick one of the two alternatives:
example (P Q : Prop) : P ∨ Q :=
begin
left,
sorry,
end
example (P Q : Prop) : P ∨ Q :=
begin
right,
sorry,
end

-- Conditional Goal
-- Use `intro`:
example (P Q : Prop) : P → Q :=
begin
intro H, -- you can give the hypothesis any name you want
sorry,
end

-- Universal Goal
-- Use `intro`:
example (U : Type) (P : U → Prop) : ∀ (x : U), P x :=
begin
intro x, -- you can rename the variable x if necessary
sorry,
end

-- Existential Goal
-- Use `existsi`:
example (U : Type) (P : U → Prop) : ∃ (x : U), P x :=
begin
existsi (sorry : U), -- you need to figure out what to put in
sorry,
end

---------------------------------
-- BASIC GIVEN TRANSFORMATIONS --
---------------------------------

-- Conjunctive Hypothesis
-- Use `cases`:
example (P Q R : Prop) (H : P ∧ Q) : R :=
begin
cases H with H₁ H₂,
sorry,
end

-- Disjunctive Hypothesis
-- Use `cases`:
example (P Q R : Prop) (H : P ∨ Q) : R :=
begin
cases H with H₁ H₂,
-- you can use braces to separate the two resulting goals.
{ sorry },
{ sorry },
end

-- Conditional Hypothesis
-- Use `apply`:
example (P Q : Prop) (H : P → Q) : Q :=
begin
apply H,
sorry,
end

-- Existential Hypothesis
-- Use `cases`:
example (U : Type) (P : U → Prop) (R : Prop)
  (H : ∃ (x : U), P x) : R :=
begin
cases H with x Hx, -- you can use any name you want for x
sorry,
end

-- Universal Hypothesis
-- Use `apply`:
example (U : Type) (P : U → Prop)
  (H : ∀ (x : U), P x) (a : U) : P a :=
begin
apply H,
end

-----------------------
-- COMMON IDENTITIES --
-----------------------

#check add_assoc -- (a + b) + c = a + (b + c)
#check add_comm -- a + b = b + a
#check add_zero -- a + 0 = a
#check zero_add -- 0 + a = a
#check mul_assoc -- (a * b) * c = a * (b * c)
#check mul_comm -- a * b = b * a
#check mul_one -- a * 1 = a
#check one_mul -- 1 * a = a
#check mul_zero -- a * 0 = 0
#check zero_mul -- 0 * a = 0
#check add_mul -- (a + b) * c = a * c + b * c
#check mul_add -- a * (b + c) = a * b + a * c

-------------------
-- COMMON LEMMAS --
-------------------

#check le_refl -- a ≤ a
#check le_antisymm -- a ≤ b → b ≤ a → a = b
#check le_trans -- a ≤ b → b ≤ c → a ≤ c
#check lt_irrefl -- ¬(a < a)
#check lt_asymm -- a < b → ¬(b < a)
#check ne_of_lt -- a < b → a ≠ b
#check le_of_eq -- a = b → a ≤ b
#check le_of_lt -- a < b → a ≤ b
#check le_of_not_gt -- ¬(a > b) → a ≤ b
#check lt_of_not_ge -- ¬(a ≤ b) → a < b
#check lt_of_lt_of_le -- a < b → b ≤ c → a < c
#check lt_of_le_of_lt -- a ≤ b → b < c → a < c
#check add_le_add -- a ≤ b → c ≤ d → a + c ≤ b + d
#check add_le_add_left -- a ≤ b → (∀ c, c + a ≤ c + b)
#check add_le_add_right -- a ≤ b → (∀ c, a + c ≤ b + c)
#check add_lt_add -- a < b → c < c → a + c < b + d
#check add_lt_add_left -- a < b → (∀ c, c + a < c + b)
#check add_lt_add_right -- a < b → (∀ c, a + c < b + c)
#check mul_lt_mul_of_pos_left -- a < b → 0 < c → c * a < c * b
#check mul_lt_mul_of_pos_right -- a < b → 0 < c → a * c < b * c
#check mul_lt_mul_of_neg_left -- b < a → c < 0 → c * a < c * b
#check mul_lt_mul_of_neg_right -- b < a → c < 0 → a * c < b * c
#check mul_le_mul_of_nonneg_left -- a ≤ b → 0 ≤ c → c * a ≤ c * b
#check mul_le_mul_of_nonneg_right -- a ≤ b → 0 ≤ c → a * c ≤ b * c
#check mul_le_mul_of_nonpos_left -- b ≤ a → c ≤ 0 → c * a ≤ c * b
#check mul_le_mul_of_nonpos_right -- b ≤ a → c ≤ 0 → a * c ≤ b * c
#check mul_pos -- a > 0 → b > 0 → a * b > 0
#check mul_neg_of_pos_of_neg -- a > 0 → b < 0 → a * b < 0
#check mul_neg_of_neg_of_pos -- a < 0 → b > 0 → a * b < 0
#check mul_pos_of_neg_of_neg -- a < 0 → b < 0 → a * b > 0
#check mul_nonneg -- a ≥ b → b ≥ 0 → a * b ≥ 0
#check mul_nonpos_of_nonneg_of_nonpos -- a ≥ 0 → b ≤ 0 → a * b ≤ 0
#check mul_nonpos_of_nonneg_of_nonpos -- a ≤ 0 → b ≥ 0 → a * b ≤ 0
#check mul_nonneg_of_nonpos_of_nonpos -- a ≤ 0 → b ≤ 0 → a * b ≥ 0
