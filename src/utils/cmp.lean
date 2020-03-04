
section
variables {α : Type*} [semiring α]

theorem mul_two_eq_add_self (x : α) : x * 2 = x + x :=
show x * (1 + 1) = x + x, by rw [mul_add, mul_one]

theorem two_mul_eq_add_self (x : α) : 2 * x = x + x :=
show (1 + 1) * x = x + x, by rw [add_mul, one_mul]

end

namespace linear_ordered_ring
variables (α : Type*) [i : linear_ordered_ring α]
include i

lemma one_pos : (0:α) < 1 := zero_lt_one α

lemma two_pos : (0:α) < 2 := _root_.add_pos (one_pos α) (one_pos α)

variable {α}

lemma add_pos (x y : α) : 0 < x → 0 < y → 0 < x + y := _root_.add_pos

lemma succ_pos (x : α) : 0 < x → 0 < x + 1 := λ h, add_pos x 1 h (one_pos α)

-- linear_ordered_ring.mul_pos (x y : α) : 0 < x → 0 < y → 0 < x * y

lemma bit0_pos (x : α) : 0 < x → 0 < bit0 x := λ h, add_pos x x h h

lemma bit1_pos (x : α) : 0 < x → 0 < bit1 x := λ h, succ_pos (bit0 x) (bit0_pos x h)

class num_pos (x : α) := (elim : (0:α) < x)

namespace num_pos
variable {i}

@[priority 30] instance one : @num_pos α i (1:α) := ⟨one_pos α⟩
@[priority 30] instance two : @num_pos α i (2:α) := ⟨two_pos α⟩
@[priority 30] instance bit0 (x : α) [@num_pos α i x] : @num_pos α i (bit0 x) := ⟨bit0_pos x (elim x)⟩
@[priority 30] instance bit1 (x : α) [@num_pos α i x] : @num_pos α i (bit1 x) := ⟨bit1_pos x (elim x)⟩
@[priority 10] instance succ (x : α) [@num_pos α i x] : @num_pos α i (x+1) := ⟨succ_pos x (elim x)⟩
@[priority 20] instance add (x y : α) [@num_pos α i x] [@num_pos α i y] : @num_pos α i (x + y) := ⟨add_pos x y (elim x) (elim y)⟩
@[priority 30] instance mul (x y : α) [@num_pos α i x] [@num_pos α i y] : @num_pos α i (x * y) := ⟨mul_pos x y (elim x) (elim y)⟩

end num_pos

class num_nonzero (x : α) := (elim : x ≠ (0:α))

@[priority 30] instance of_pos (x : α) {i : linear_ordered_ring α} [@num_pos α i x] : num_nonzero x := ⟨ne_of_gt $ num_pos.elim x⟩

end linear_ordered_ring

theorem pos_trivial {α : Type*} [linear_ordered_ring α] (x : α) [linear_ordered_ring.num_pos x] : (0:α) < x := linear_ordered_ring.num_pos.elim x
theorem nonzero_trivial {α : Type*} [linear_ordered_ring α] (x : α) [linear_ordered_ring.num_nonzero x] : x ≠ 0 := linear_ordered_ring.num_nonzero.elim x

section
variables {α : Type*} [linear_ordered_ring α]

theorem le_of_mul_ge_mul_left {a b c : α} : c * b ≤ c * a → c < 0 → a ≤ b :=
begin
intros h hc,
have hc : -c > 0 := neg_pos_of_neg hc,
apply le_of_mul_le_mul_left _ hc,
apply le_of_neg_le_neg,
rw [neg_mul_eq_neg_mul, neg_mul_eq_neg_mul, neg_neg],
assumption,
end

theorem le_of_mul_ge_mul_right {a b c : α} : b * c ≤ a * c → c < 0 → a ≤ b :=
begin
intros h hc,
have hc : -c > 0 := neg_pos_of_neg hc,
apply le_of_mul_le_mul_right _ hc,
apply le_of_neg_le_neg,
rw [neg_mul_eq_mul_neg, neg_mul_eq_mul_neg, neg_neg],
assumption,
end

end

section
variables {α : Type*} [linear_ordered_field α]

theorem div_le_of_le_mul_of_pos {x y : α} (z : α) : x ≤ y*z → 0 < z → x/z ≤ y :=
begin
intros hm hz,
apply le_of_mul_le_mul_right _ hz,
transitivity x,
{ apply le_of_eq,
  apply div_mul_cancel,
  apply ne_of_gt,
  assumption },
{ assumption },
end

theorem le_div_of_mul_le_of_pos {x y : α} (z : α) : x*z ≤ y → 0 < z → x ≤ y/z :=
begin
intros hm hz,
apply le_of_mul_le_mul_right _ hz,
transitivity y,
{ assumption },
{ apply le_of_eq,
  symmetry,
  apply div_mul_cancel,
  apply ne_of_gt,
  assumption },
end

theorem le_div_of_mul_ge_of_neg {x y : α} (z : α) : y ≤ x*z → z < 0 → x ≤ y/z :=
begin
intros hm hz,
apply le_of_mul_ge_mul_right _ hz,
transitivity y,
{ apply le_of_eq,
  apply div_mul_cancel,
  apply ne_of_lt,
  assumption },
{ assumption },
end

theorem div_le_of_ge_mul_of_neg {x y : α} (z : α) : y*z ≤ x → z < 0 → x/z ≤ y :=
begin
intros hm hz,
apply le_of_mul_ge_mul_right _ hz,
transitivity x,
{ assumption },
{ apply le_of_eq,
  symmetry,
  apply div_mul_cancel,
  apply ne_of_lt,
  assumption },
end

end

namespace order

inductive {u} lt_cmp {α : Type u} [has_lt α] (x y : α) : Type u
| eq : x = y → lt_cmp
| lt : x < y → lt_cmp
| gt : y < x → lt_cmp

inductive {u} le_cmp {α : Type u} [has_le α] (x y : α) : Type u
| le : x ≤ y → le_cmp
| ge : y ≤ x → le_cmp

variables {α : Type*} [decidable_linear_order α]

def lt_compare (x y : α) : lt_cmp x y :=
if hlt : x < y then
lt_cmp.lt hlt
else if hgt : y < x then
lt_cmp.gt hgt
else
lt_cmp.eq $ le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

def le_compare (x y : α) : le_cmp x y :=
if h : x < y then
le_cmp.le (le_of_lt h)
else
le_cmp.ge (le_of_not_gt h)

@[elab_as_eliminator]
def trichotomy_on (x y : α) {C : Sort*} : (x = y → C) → (x < y → C) → (y < x → C) → C :=
λ heq hlt hgt, lt_cmp.cases_on (lt_compare x y) heq hlt hgt

@[elab_as_eliminator]
def dichotomy_on (x y : α) {C : Sort*} : (x ≤ y → C) → (y ≤ x → C) → C :=
λ hle hge, le_cmp.cases_on (le_compare x y) hle hge

end order

namespace tactic
open interactive

/--
`by_trichotomy (x, y)` splits the goal into three branches, the first assuming `x = y`,
the second assuming `x < y` and the third assuming `y < x`.

This tactic requires that terms `x` and `y` have the same type and that this type has 
`decidable_linear_order` instance.
-/
meta def interactive.by_trichotomy : parse types.texpr → tactic unit :=
λ e, do {
  `(@prod.mk %%t %%.(t) %%x %%y) ← to_expr e,
  d ← to_expr ``(decidable_linear_order %%t) >>= mk_instance
    <|> fail ("cannot find decidable_linear_order instance for type " ++ to_string t),
  to_expr ``(@order.trichotomy_on %%t %%d %%x %%y) >>= apply >> skip
}

/--
`by_trichotomy (x, y)` splits the goal into two branches, the first assuming `x ≤ y`
and the second assuming `y ≤ x`.

This tactic requires that terms `x` and `y` have the same type and that this type has 
`decidable_linear_order` instance.
-/
meta def interactive.by_dichotomy : parse types.texpr → tactic unit :=
λ e, do {
  `(@prod.mk %%t %%.(t) %%x %%y) ← to_expr e,
  d ← to_expr ``(decidable_linear_order %%t) >>= mk_instance
    <|> fail ("cannot find decidable_linear_order instance for " ++ to_string t),
  to_expr ``(@order.dichotomy_on %%t %%d %%x %%y) >>= apply >> skip
}

end tactic
